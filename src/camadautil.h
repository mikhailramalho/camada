#ifndef CAMADAUTIL_H_
#define CAMADAUTIL_H_

#include <bitset>
#include <cstdint>
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

} // namespace camada

#endif
