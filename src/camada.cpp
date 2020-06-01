#include "camada.h"
#include "ac_config.h"

#include <fmt/printf.h>

const std::string getCamadaVersion() { return CAMADA_VERSION; }

void abortCondWithMessage(const std::string Msg, bool Cond) {
  if (!Cond) {
    fmt::print(stderr, Msg + "\n");
    abort();
  }
}

void camada::SMTSort::dump() const {
  fmt::printf("SMTSort dump not implemented.\n");
}

void camada::SMTExpr::dump() const {
  fmt::printf("SMTExpr dump not implemented.\n");
}

void camada::SMTSolver::dump() const {
  fmt::printf("SMTSolver dump not implemented.\n");
}

void camada::SMTSolver::dumpModel() const {
  fmt::printf("SMTSolver model dump not implemented.\n");
}
