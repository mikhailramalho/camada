/**************************************************************************
 *
 * Licensed to the Apache Software Foundation (ASF) under one
 * or more contributor license agreements.  See the NOTICE file
 * distributed with this work for additional information
 * regarding copyright ownership.  The ASF licenses this file
 * to you under the Apache License, Version 2.0 (the
 * "License"); you may not use this file except in compliance
 * with the License.  You may obtain a copy of the License at
 *
 * http://www.apache.org/licenses/LICENSE-2.0
 *
 * Unless required by applicable law or agreed to in writing,
 * software distributed under the License is distributed on an
 * "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY
 * KIND, either express or implied.  See the License for the
 * specific language governing permissions and limitations
 * under the License.
 *
 **************************************************************************/

// Finds the hardest-to-round input for exp() over a fixed-point format:
// the input whose exact exp() lands closest to a halfway point between two
// representable values. That distance is what decides how wide an
// intermediate a correctly-rounded encoding needs, so measuring it turns
// the table maker's dilemma into a settled fact rather than an estimate.
//
// The search is exhaustive. Only a narrow band of inputs matters — below
// it exp() rounds to zero, above it saturates — but that band still holds
// ~9.5e10 inputs for the 64-bit format, so the sweep is written to be
// fast rather than obvious:
//
//   exp((r+1)/2^n) = exp(r/2^n) * exp(2^-n)
//
// turns one transcendental per input into one multiply. Each chunk
// re-anchors with a fresh exp() so the rounding error of the chained
// multiplies cannot accumulate across the whole run; within a chunk the
// error stays far below the distances being measured (at the default
// precision, ~2^-120 after a whole chunk, against distances near 2^-21).
//
// Usage: fxp-exp-worstcase <width> <frac_bits> [threads] [precision]
//   e.g. fxp-exp-worstcase 32 15        # accum
//        fxp-exp-worstcase 64 31 32     # long accum on 32 threads

#include <inttypes.h>
#include <limits.h>
#include <mpfr.h>
#include <pthread.h>
#include <stdbool.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

// Inputs are re-anchored this often, bounding the error of the chained
// multiplies to a single chunk's worth.
#define ANCHOR_STRIDE 1000000L

struct Range {
  long Lo, Hi; // inclusive raw-input bounds
};

struct Task {
  struct Range R;
  unsigned FracBits;
  mpfr_prec_t Prec;
  // results
  mpfr_t Best;
  long BestRaw;
};

// Distance from v to the nearest halfway point between representable
// values, measured in units of the format's ulp: |frac(v * 2^n) - 1/2|.
static void halfwayDistance(mpfr_t Out, const mpfr_t Value, unsigned FracBits,
                            mpfr_t Scratch, const mpfr_t Half) {
  mpfr_mul_2ui(Scratch, Value, FracBits, MPFR_RNDN);
  mpfr_frac(Out, Scratch, MPFR_RNDN);
  mpfr_sub(Out, Out, Half, MPFR_RNDN);
  mpfr_abs(Out, Out, MPFR_RNDN);
}

static void *sweep(void *Arg) {
  struct Task *T = (struct Task *)Arg;
  mpfr_t Cur, Step, Scratch, Dist, Half, X;
  mpfr_inits2(T->Prec, Cur, Step, Scratch, Dist, Half, X, (mpfr_ptr)0);
  mpfr_set_d(Half, 0.5, MPFR_RNDN);

  // exp(2^-n), the ratio between consecutive inputs.
  mpfr_set_ui(Step, 1, MPFR_RNDN);
  mpfr_div_2ui(Step, Step, T->FracBits, MPFR_RNDN);
  mpfr_exp(Step, Step, MPFR_RNDN);

  mpfr_set_ui(T->Best, 1, MPFR_RNDN);
  T->BestRaw = T->R.Lo;

  for (long Anchor = T->R.Lo; Anchor <= T->R.Hi; Anchor += ANCHOR_STRIDE) {
    long End = Anchor + ANCHOR_STRIDE - 1;
    if (End > T->R.Hi)
      End = T->R.Hi;
    // Fresh exp() per chunk: the chained multiplies below never carry
    // their rounding error past this point.
    mpfr_set_si(X, Anchor, MPFR_RNDN);
    mpfr_div_2ui(X, X, T->FracBits, MPFR_RNDN);
    mpfr_exp(Cur, X, MPFR_RNDN);

    for (long Raw = Anchor; Raw <= End; ++Raw) {
      halfwayDistance(Dist, Cur, T->FracBits, Scratch, Half);
      if (mpfr_cmp(Dist, T->Best) < 0) {
        mpfr_set(T->Best, Dist, MPFR_RNDN);
        T->BestRaw = Raw;
      }
      mpfr_mul(Cur, Cur, Step, MPFR_RNDN);
    }
  }
  mpfr_clears(Cur, Step, Scratch, Dist, Half, X, (mpfr_ptr)0);
  return NULL;
}

// Below Lo, exp(x) rounds to zero; above Hi it saturates. Both bounds are
// computed generously (one ulp of slack either way) so the swept band is a
// superset of the inputs whose result is neither 0 nor MAX.
static struct Range interestingRange(unsigned Width, unsigned FracBits,
                                     bool IsSigned, mpfr_prec_t Prec) {
  mpfr_t V, L;
  mpfr_inits2(Prec, V, L, (mpfr_ptr)0);
  struct Range R;

  // exp(x) < 2^-(n+1)  =>  rounds to zero.
  mpfr_set_ui(V, 1, MPFR_RNDN);
  mpfr_div_2ui(V, V, FracBits + 1, MPFR_RNDN);
  mpfr_log(L, V, MPFR_RNDN);
  mpfr_mul_2ui(L, L, FracBits, MPFR_RNDN);
  R.Lo = mpfr_get_si(L, MPFR_RNDD) - 1;

  // exp(x) > maxRaw / 2^n  =>  saturates. maxRaw is 2^(w-1)-1 signed,
  // 2^w-1 unsigned.
  mpfr_set_ui(V, 1, MPFR_RNDN);
  mpfr_mul_2ui(V, V, IsSigned ? Width - 1 : Width, MPFR_RNDN);
  mpfr_sub_ui(V, V, 1, MPFR_RNDN);
  mpfr_div_2ui(V, V, FracBits, MPFR_RNDN);
  mpfr_log(L, V, MPFR_RNDN);
  mpfr_mul_2ui(L, L, FracBits, MPFR_RNDN);
  R.Hi = mpfr_get_si(L, MPFR_RNDU) + 1;

  // Clamp to what the format can actually hold. An unsigned format has no
  // negative inputs at all, so the whole exp(x) < 1 half of the band is
  // unreachable and the sweep must start at zero. At Width 64 the signed
  // format spans the whole of long, so computing its bounds would
  // overflow and the clamp is vacuous anyway.
  long FmtLo = 0, FmtHi = LONG_MAX;
  if (IsSigned) {
    if (Width < 64) {
      FmtLo = -(1L << (Width - 1));
      FmtHi = (1L << (Width - 1)) - 1;
    } else {
      FmtLo = LONG_MIN;
    }
  } else if (Width < 63) {
    FmtHi = (1L << Width) - 1;
  }
  if (R.Lo < FmtLo)
    R.Lo = FmtLo;
  if (R.Hi > FmtHi)
    R.Hi = FmtHi;
  mpfr_clears(V, L, (mpfr_ptr)0);
  return R;
}

int main(int argc, char **argv) {
  if (argc < 4) {
    fprintf(stderr,
            "usage: %s <width> <frac_bits> <s|u> [threads] [precision]\n"
            "  e.g. %s 32 15 s        (accum)\n"
            "       %s 64 31 s 32     (long accum, 32 threads)\n"
            "       %s 32 16 u 32     (unsigned accum)\n",
            argv[0], argv[0], argv[0], argv[0]);
    return 2;
  }
  unsigned Width = (unsigned)strtoul(argv[1], NULL, 10);
  unsigned FracBits = (unsigned)strtoul(argv[2], NULL, 10);
  bool IsSigned = argv[3][0] == 's';
  if (argv[3][0] != 's' && argv[3][0] != 'u') {
    fprintf(stderr, "signedness must be 's' or 'u'\n");
    return 2;
  }
  long Threads = argc > 4 ? strtol(argv[4], NULL, 10) : 1;
  mpfr_prec_t Prec = argc > 5 ? (mpfr_prec_t)strtol(argv[5], NULL, 10) : 192;
  if (Width < 2 || Width > 64 || FracBits > Width ||
      (IsSigned && FracBits >= Width) || Threads < 1) {
    fprintf(stderr, "invalid format or thread count\n");
    return 2;
  }

  struct Range Full = interestingRange(Width, FracBits, IsSigned, Prec);
  long Count = Full.Hi - Full.Lo + 1;
  printf("format %c%u.%u: sweeping raw %ld..%ld (%ld inputs) on %ld thread(s),"
         " precision %ld\n",
         IsSigned ? 's' : 'u', IsSigned ? Width - FracBits - 1 : Width - FracBits,
         FracBits, Full.Lo, Full.Hi, Count, Threads, (long)Prec);
  fflush(stdout);

  struct Task *Tasks = (struct Task *)calloc((size_t)Threads, sizeof(*Tasks));
  pthread_t *Ts = (pthread_t *)calloc((size_t)Threads, sizeof(*Ts));
  if (!Tasks || !Ts) {
    fprintf(stderr, "out of memory\n");
    return 1;
  }
  long Per = (Count + Threads - 1) / Threads;
  for (long I = 0; I < Threads; ++I) {
    Tasks[I].R.Lo = Full.Lo + I * Per;
    Tasks[I].R.Hi = Tasks[I].R.Lo + Per - 1;
    if (Tasks[I].R.Hi > Full.Hi)
      Tasks[I].R.Hi = Full.Hi;
    Tasks[I].FracBits = FracBits;
    Tasks[I].Prec = Prec;
    mpfr_init2(Tasks[I].Best, Prec);
    mpfr_set_ui(Tasks[I].Best, 1, MPFR_RNDN);
    Tasks[I].BestRaw = Tasks[I].R.Lo;
    if (Tasks[I].R.Lo > Full.Hi) // more threads than work
      Tasks[I].R.Hi = Tasks[I].R.Lo - 1;
    pthread_create(&Ts[I], NULL, sweep, &Tasks[I]);
  }

  mpfr_t Best;
  mpfr_init2(Best, Prec);
  mpfr_set_ui(Best, 1, MPFR_RNDN);
  long BestRaw = 0;
  for (long I = 0; I < Threads; ++I) {
    pthread_join(Ts[I], NULL);
    if (Tasks[I].R.Hi >= Tasks[I].R.Lo &&
        mpfr_cmp(Tasks[I].Best, Best) < 0) {
      mpfr_set(Best, Tasks[I].Best, MPFR_RNDN);
      BestRaw = Tasks[I].BestRaw;
    }
    mpfr_clear(Tasks[I].Best);
  }

  // Report the distance in bits: an encoding whose intermediate carries
  // more than this many fractional bits can always decide the rounding.
  mpfr_t Bits;
  mpfr_init2(Bits, Prec);
  mpfr_log2(Bits, Best, MPFR_RNDN);
  mpfr_neg(Bits, Bits, MPFR_RNDN);
  printf("hardest-to-round input: raw=%ld\n", BestRaw);
  printf("  distance to halfway: %.10e  (2^-%.4f)\n",
         mpfr_get_d(Best, MPFR_RNDN), mpfr_get_d(Bits, MPFR_RNDN));
  printf("  => an intermediate with %u fractional bits decides every "
         "rounding\n",
         FracBits + (unsigned)mpfr_get_d(Bits, MPFR_RNDN) + 2);

  mpfr_clears(Best, Bits, (mpfr_ptr)0);
  free(Tasks);
  free(Ts);
  return 0;
}
