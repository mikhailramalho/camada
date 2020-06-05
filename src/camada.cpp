#include "camada.h"
#include "ac_config.h"

#include <fmt/printf.h>

std::string camada::getCamadaVersion() { return CAMADA_VERSION; }

[[noreturn]] void camada::abortWithMessage(const std::string &Msg) {
  fmt::print(stderr, Msg + "\n");
  abort();
}

void camada::abortCondWithMessage(bool Cond, const std::string &Msg) {
  if (!Cond)
    abortWithMessage(Msg);
}

void camada::SMTSort::dump() const {
  fmt::printf("SMTSort dump not implemented.\n");
}

void camada::SMTExpr::dump() const {
  fmt::printf("SMTExpr dump not implemented.\n");
}

void camada::SMTSolver::dump() {
  fmt::printf("SMTSolver dump not implemented.\n");
}

void camada::SMTSolver::dumpModel() {
  fmt::printf("SMTSolver model dump not implemented.\n");
}
