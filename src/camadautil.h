#ifndef CAMADAUTIL_H_
#define CAMADAUTIL_H_

#include <bitset>
#include <cassert>
#include <cstdint>
#include <cstring>
#include <string>

namespace camada {

static inline std::string toTwosComplementBin(int64_t Value, unsigned Width) {
  const uint64_t RawBits = static_cast<uint64_t>(Value);
  std::string Bits = std::bitset<64>(RawBits).to_string();
  if (Width < 64)
    Bits = Bits.substr(64 - Width);
  else if (Width > 64)
    Bits.insert(Bits.begin(), Width - 64, Value < 0 ? '1' : '0');
  return Bits;
}

template <typename FPType, typename IntType>
static inline FPType IntAsFP(const IntType Int) {
  assert(sizeof(FPType) == sizeof(IntType) &&
         "Cannot convert int to floating-point");

  FPType Result;
  std::memcpy(&Result, &Int, sizeof(IntType));
  return Result;
}

template <typename FPType, typename IntType>
static inline IntType FPAsInt(const FPType FP) {
  assert(sizeof(FPType) == sizeof(IntType) &&
         "Cannot convert int to floating-point");

  IntType Result;
  std::memcpy(&Result, &FP, sizeof(FPType));
  return Result;
}

} // namespace camada

#endif
