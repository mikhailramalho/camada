#!/usr/bin/env python3
"""Generates the fixed-point execution-oracle tables.

Emits a C program exercising Clang's -ffixed-point arithmetic over
boundary and pseudo-random operand vectors, compiles it with the pinned
Clang, executes it natively, and writes the observed raw result bits to
regression/fxp_oracle_tables.h for the camada regression fixture to
cross-check the BV encoding against.

UB cases are filtered out before emission using an exact big-integer
reference (Python ints): non-saturating overflow, division by zero, and
overflowing non-saturating shifts are undefined in C, so executing them
would produce garbage, not an oracle. Saturating ops need no filtering.

Determinism: fixed PRNG seed; the output header records the generating
Clang version, target, flags, and seed.

Usage: fxp_oracle_gen.py --clang /path/to/clang [--out FILE]
"""

import argparse
import random
import subprocess
import sys
import tempfile
from pathlib import Path

# The x86_64-unknown-linux default ladder (Clang TargetInfo), padding off.
# (c_type, width, frac_bits, is_signed)
FORMATS = [
    ("short _Fract", 8, 7, True),
    ("_Fract", 16, 15, True),
    ("long _Fract", 32, 31, True),
    ("short _Accum", 16, 7, True),
    ("_Accum", 32, 15, True),
    ("long _Accum", 64, 31, True),
    ("unsigned short _Fract", 8, 8, False),
    ("unsigned _Fract", 16, 16, False),
    ("unsigned long _Fract", 32, 32, False),
    ("unsigned short _Accum", 16, 8, False),
    ("unsigned _Accum", 32, 16, False),
    ("unsigned long _Accum", 64, 32, False),
]

# Compile-time layout checks emitted into the C program: any target whose
# defaults diverge from the table above fails the build instead of
# generating wrong tables.
LAYOUT_ASSERTS = """
_Static_assert(__SFRACT_FBIT__ == 7, "sfract");
_Static_assert(__FRACT_FBIT__ == 15, "fract");
_Static_assert(__LFRACT_FBIT__ == 31, "lfract");
_Static_assert(__SACCUM_FBIT__ == 7 && __SACCUM_IBIT__ == 8, "saccum");
_Static_assert(__ACCUM_FBIT__ == 15 && __ACCUM_IBIT__ == 16, "accum");
_Static_assert(__LACCUM_FBIT__ == 31 && __LACCUM_IBIT__ == 32, "laccum");
_Static_assert(__USFRACT_FBIT__ == 8, "usfract");
_Static_assert(__UFRACT_FBIT__ == 16, "ufract");
_Static_assert(__ULFRACT_FBIT__ == 32, "ulfract");
_Static_assert(__USACCUM_FBIT__ == 8 && __USACCUM_IBIT__ == 8, "usaccum");
_Static_assert(__UACCUM_FBIT__ == 16 && __UACCUM_IBIT__ == 16, "uaccum");
_Static_assert(__ULACCUM_FBIT__ == 32 && __ULACCUM_IBIT__ == 32, "ulaccum");
_Static_assert(sizeof(short _Fract) == 1 && sizeof(_Fract) == 2 &&
               sizeof(long _Fract) == 4 && sizeof(short _Accum) == 2 &&
               sizeof(_Accum) == 4 && sizeof(long _Accum) == 8, "sizes");
"""

BINARY_OPS = ["add", "sub", "mul", "div"]
UNARY_OPS = ["neg"]
SHIFT_OPS = ["shl", "shr"]
SAT_SUFFIX = "_sat"


def min_raw(w, s):
    return -(1 << (w - 1)) if s else 0


def max_raw(w, s):
    return (1 << (w - 1)) - 1 if s else (1 << w) - 1


def wrap(v, w):
    return v & ((1 << w) - 1)


def decode(raw, w, s):
    raw = wrap(raw, w)
    if s and raw >> (w - 1):
        return raw - (1 << w)
    return raw


def boundary_values(w, n, s):
    vals = {0, 1, 2, wrap(min_raw(w, s), w), wrap(max_raw(w, s), w),
            wrap(min_raw(w, s) + 1, w), wrap(max_raw(w, s) - 1, w)}
    if n < w:
        vals.add(wrap(1 << n, w))  # 1.0 where representable
    vals.add(wrap((1 << n) - 1, w))  # just under 1.0
    vals.add(wrap(0xAAAAAAAAAAAAAAAA, w))
    vals.add(wrap(0x5555555555555555, w))
    return sorted(vals)


# --- exact reference (UB filter only; results come from execution) --------


def exact_overflows(op, a, b, w, n, s):
    lo, hi = min_raw(w, s), max_raw(w, s)
    if op == "add":
        return not lo <= a + b <= hi
    if op == "sub":
        return not lo <= a - b <= hi
    if op == "neg":
        return not lo <= -a <= hi
    if op == "mul":
        return not lo * (1 << n) <= a * b <= hi * (1 << n)
    if op == "div":
        num = a << n
        return not (min(lo * b, hi * b) <= num <= max(lo * b, hi * b))
    raise AssertionError(op)


def shift_overflows(op, a, k, w, n, s):
    if op == "shr":
        return False
    lo, hi = min_raw(w, s), max_raw(w, s)
    return not lo <= a * (1 << k) <= hi


# --- C program emission ----------------------------------------------------


def int_type(w):
    return f"uint{w}_t"


def emit_case_fn(idx, ctype, w, n, s, op, sat, vectors):
    """One function per (format, op): a static vector table iterated at
    runtime, computing with real fixed-point types and printing raw bits."""
    qual = f"_Sat {ctype}" if sat else ctype
    it = int_type(w)
    lines = []
    lines.append(f"static void case_{idx}(void) {{")
    if op in BINARY_OPS:
        rows = ",".join(f"{{{a}ull,{b}ull}}" for a, b in vectors)
        lines.append(f"  static const struct {{ uint64_t a, b; }} v[] = {{{rows}}};")
        lines.append(f"  for (unsigned i = 0; i < {len(vectors)}u; ++i) {{")
        lines.append(f"    {it} ra = ({it})v[i].a, rb = ({it})v[i].b, rr;")
        lines.append(f"    {qual} a, b, r;")
        lines.append("    memcpy(&a, &ra, sizeof a); memcpy(&b, &rb, sizeof b);")
        sym = {"add": "+", "sub": "-", "mul": "*", "div": "/"}[op]
        lines.append(f"    r = a {sym} b;")
        lines.append("    memcpy(&rr, &r, sizeof r);")
    elif op in UNARY_OPS:
        rows = ",".join(f"{a}ull" for (a,) in vectors)
        lines.append(f"  static const uint64_t v[] = {{{rows}}};")
        lines.append(f"  for (unsigned i = 0; i < {len(vectors)}u; ++i) {{")
        lines.append(f"    {it} ra = ({it})v[i], rb = 0, rr;")
        lines.append(f"    {qual} a, r;")
        lines.append("    memcpy(&a, &ra, sizeof a);")
        lines.append("    r = -a;")
        lines.append("    memcpy(&rr, &r, sizeof r);")
    else:  # shifts: vector rows are (raw, amount)
        rows = ",".join(f"{{{a}ull,{k}ull}}" for a, k in vectors)
        lines.append(f"  static const struct {{ uint64_t a, b; }} v[] = {{{rows}}};")
        lines.append(f"  for (unsigned i = 0; i < {len(vectors)}u; ++i) {{")
        lines.append(f"    {it} ra = ({it})v[i].a, rb = ({it})v[i].b, rr;")
        lines.append(f"    {qual} a, r;")
        lines.append("    memcpy(&a, &ra, sizeof a);")
        sym = "<<" if op == "shl" else ">>"
        lines.append(f"    r = a {sym} (int)v[i].b;")
        lines.append("    memcpy(&rr, &r, sizeof r);")
    opname = op + (SAT_SUFFIX if sat else "")
    lines.append(
        f'    printf("{opname},{w},{n},{int(s)},%llu,%llu,%llu\\n",'
        "(unsigned long long)ra,(unsigned long long)rb,(unsigned long long)rr);")
    lines.append("  }")
    lines.append("}")
    return "\n".join(lines)


def emit_conv_fn(idx, from_fmt, to_fmt, vectors):
    (fc, fw, fn, fs) = from_fmt
    (tc, tw, tn, ts) = to_fmt
    fit, tit = int_type(fw), int_type(tw)
    rows = ",".join(f"{a}ull" for a in vectors)
    body = f"""static void case_{idx}(void) {{
  static const uint64_t v[] = {{{rows}}};
  for (unsigned i = 0; i < {len(vectors)}u; ++i) {{
    {fit} ra = ({fit})v[i]; {tit} rr;
    {fc} a; _Sat {tc} r;
    memcpy(&a, &ra, sizeof a);
    r = a;
    memcpy(&rr, &r, sizeof r);
    printf("cvt_sat,{fw},{fn},{int(fs)},%llu,{tw}.{tn}.{int(ts)},%llu\\n",
           (unsigned long long)ra, (unsigned long long)rr);
  }}
}}"""
    return body


def emit_tobv_fn(idx, from_fmt, to_w, to_signed, vectors):
    (fc, fw, fn, fs) = from_fmt
    fit = int_type(fw)
    tint = f"int{to_w}_t" if to_signed else f"uint{to_w}_t"
    rows = ",".join(f"{a}ull" for a in vectors)
    body = f"""static void case_{idx}(void) {{
  static const uint64_t v[] = {{{rows}}};
  for (unsigned i = 0; i < {len(vectors)}u; ++i) {{
    {fit} ra = ({fit})v[i];
    {fc} a;
    memcpy(&a, &ra, sizeof a);
    {tint} r = ({tint})a;
    printf("tobv,{fw},{fn},{int(fs)},%llu,{to_w}.{int(to_signed)},%llu\\n",
           (unsigned long long)ra,
           (unsigned long long)(uint{to_w}_t)r);
  }}
}}"""
    return body


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--clang", required=True)
    ap.add_argument("--out", default="regression/fxp_oracle_tables.h")
    ap.add_argument("--seed", type=int, default=0xCA3ADA)
    ap.add_argument("--randoms", type=int, default=24)
    args = ap.parse_args()

    rng = random.Random(args.seed)
    fns = []
    idx = 0

    for (ctype, w, n, s) in FORMATS:
        bounds = boundary_values(w, n, s)
        rand_raws = [rng.getrandbits(w) for _ in range(args.randoms)]
        singles = bounds + rand_raws
        pair_anchors = [0, 1, wrap(min_raw(w, s), w), wrap(max_raw(w, s), w)]
        pairs = [(a, b) for a in singles for b in pair_anchors]
        pairs += [(rng.getrandbits(w), rng.getrandbits(w))
                  for _ in range(args.randoms)]

        for op in BINARY_OPS + UNARY_OPS:
            vec = pairs if op in BINARY_OPS else [(a,) for a in singles]
            # Non-saturating: filter UB (overflow, div-by-zero).
            plain = []
            for v in vec:
                a = decode(v[0], w, s)
                b = decode(v[1], w, s) if len(v) > 1 else 0
                if op == "div" and b == 0:
                    continue
                if exact_overflows(op, a, b, w, n, s):
                    continue
                plain.append(v)
            if plain:
                fns.append(emit_case_fn(idx, ctype, w, n, s, op, False, plain))
                idx += 1
            # Saturating: only div-by-zero stays UB.
            satv = [v for v in vec
                    if not (op == "div" and decode(v[1], w, s) == 0)]
            if satv:
                fns.append(emit_case_fn(idx, ctype, w, n, s, op, True, satv))
                idx += 1

        for op in SHIFT_OPS:
            amounts = sorted({1, 2, n, w - 1} - {0})
            svec = [(a, k) for a in singles for k in amounts if k < w]
            plain = [(a, k) for (a, k) in svec
                     if not shift_overflows(op, decode(a, w, s), k, w, n, s)]
            if plain:
                fns.append(emit_case_fn(idx, ctype, w, n, s, op, False, plain))
                idx += 1
            if op == "shl":  # sat variant exists for shl only
                fns.append(emit_case_fn(idx, ctype, w, n, s, op, True, svec))
                idx += 1

    # Conversions: every format pair through a _Sat target (defined for all
    # inputs, so no filtering), and fixed->int casts (toward zero, clamped
    # only by our Sat variant -- the plain C cast of an out-of-range value
    # is UB, so filter those to in-range for the unsuffixed comparison).
    for from_fmt in FORMATS:
        (fc, fw, fn_, fs) = from_fmt
        singles = boundary_values(fw, fn_, fs) + \
            [rng.getrandbits(fw) for _ in range(args.randoms)]
        for to_fmt in FORMATS:
            fns.append(emit_conv_fn(idx, from_fmt, to_fmt, singles))
            idx += 1
        for to_w in (8, 16, 32):
            for to_signed in (True, False):
                inrange = []
                for a in singles:
                    val = decode(a, fw, fs)
                    trunc = (val // (1 << fn_) if val >= 0
                             else -((-val) >> fn_))
                    if min_raw(to_w, to_signed) <= trunc <= \
                            max_raw(to_w, to_signed):
                        inrange.append(a)
                if inrange:
                    fns.append(
                        emit_tobv_fn(idx, from_fmt, to_w, to_signed, inrange))
                    idx += 1

    calls = "\n".join(f"  case_{i}();" for i in range(idx))
    prog = f"""#include <stdint.h>
#include <stdio.h>
#include <string.h>
{LAYOUT_ASSERTS}
{chr(10).join(fns)}
int main(void) {{
{calls}
  return 0;
}}
"""

    with tempfile.TemporaryDirectory() as td:
        src = Path(td) / "oracle.c"
        exe = Path(td) / "oracle"
        src.write_text(prog)
        version = subprocess.run([args.clang, "--version"], capture_output=True,
                                 text=True, check=True).stdout.splitlines()[0]
        subprocess.run([args.clang, "-ffixed-point", "-target",
                        "x86_64-unknown-linux", "-O1", "-o", str(exe),
                        str(src)], check=True)
        out = subprocess.run([str(exe)], capture_output=True, text=True,
                             check=True).stdout

    arith, convs, tobvs = [], [], []
    for line in out.splitlines():
        f = line.split(",")
        if f[0] == "cvt_sat":
            tw, tn, ts = f[5].split(".")
            convs.append((f[1], f[2], f[3], f[4], tw, tn, ts, f[6]))
        elif f[0] == "tobv":
            tw, ts = f[5].split(".")
            tobvs.append((f[1], f[2], f[3], f[4], tw, ts, f[6]))
        else:
            arith.append((f[0], f[1], f[2], f[3], f[4], f[5], f[6]))

    hdr = []
    hdr.append("// Generated by scripts/fxp_oracle_gen.py -- DO NOT EDIT.")
    hdr.append(f"// Oracle: {version}")
    hdr.append("// Flags: -ffixed-point -target x86_64-unknown-linux -O1")
    hdr.append(f"// Seed: {args.seed:#x}  Randoms/format: {args.randoms}")
    hdr.append("//")
    hdr.append("// Raw result bits observed by executing Clang-compiled")
    hdr.append("// fixed-point arithmetic. UB cases (non-saturating overflow,")
    hdr.append("// division by zero, overflowing plain shifts, out-of-range")
    hdr.append("// plain casts) are filtered out pre-generation.")
    hdr.append("#ifndef CAMADA_REGRESSION_FXP_ORACLE_TABLES_H_")
    hdr.append("#define CAMADA_REGRESSION_FXP_ORACLE_TABLES_H_")
    hdr.append("#include <cstdint>")
    hdr.append("namespace camada_fxp_oracle {")
    hdr.append("enum class OrOp : uint8_t { Add, Sub, Mul, Div, Neg, Shl,")
    hdr.append("  Shr, AddSat, SubSat, MulSat, DivSat, NegSat, ShlSat };")
    hdr.append("struct OrArith { OrOp op; uint8_t w, n, s;")
    hdr.append("  uint64_t a, b, r; };")
    opmap = {"add": "Add", "sub": "Sub", "mul": "Mul", "div": "Div",
             "neg": "Neg", "shl": "Shl", "shr": "Shr",
             "add_sat": "AddSat", "sub_sat": "SubSat", "mul_sat": "MulSat",
             "div_sat": "DivSat", "neg_sat": "NegSat", "shl_sat": "ShlSat"}
    hdr.append("inline const OrArith kArith[] = {")
    for (op, w, n, s, a, b, r) in arith:
        hdr.append(f"  {{OrOp::{opmap[op]},{w},{n},{s},{a}ull,{b}ull,{r}ull}},")
    hdr.append("};")
    hdr.append("struct OrConv { uint8_t fw, fn, fs, tw, tn, ts;")
    hdr.append("  uint64_t a, r; };")
    hdr.append("inline const OrConv kConvSat[] = {")
    for (fw, fn_, fs, a, tw, tn, ts, r) in convs:
        hdr.append(f"  {{{fw},{fn_},{fs},{tw},{tn},{ts},{a}ull,{r}ull}},")
    hdr.append("};")
    hdr.append("struct OrToBV { uint8_t fw, fn, fs, tw, ts;")
    hdr.append("  uint64_t a, r; };")
    hdr.append("inline const OrToBV kToBV[] = {")
    for (fw, fn_, fs, a, tw, ts, r) in tobvs:
        hdr.append(f"  {{{fw},{fn_},{fs},{tw},{ts},{a}ull,{r}ull}},")
    hdr.append("};")
    hdr.append("} // namespace camada_fxp_oracle")
    hdr.append("#endif")
    Path(args.out).write_text("\n".join(hdr) + "\n")
    print(f"{len(arith)} arith + {len(convs)} conv + {len(tobvs)} tobv "
          f"vectors -> {args.out}")
    print(f"oracle: {version}")


if __name__ == "__main__":
    main()
