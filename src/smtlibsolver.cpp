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

#include "smtlibsolver.h"
#include "camadacommon.h"

#include <algorithm>
#include <atomic>
#include <climits>
#include <csignal>
#include <cstdio>
#include <cstdlib>
#include <fcntl.h>
#include <string>
#include <sys/resource.h>
#include <sys/select.h>
#include <sys/syscall.h>
#include <sys/types.h>
#include <sys/wait.h>
#include <unistd.h>
#include <utility>
#include <vector>

namespace camada {

namespace {

// Render a structural SMT-LIB term to text. Subterms referenced more than
// once within one emission are bound to let temporaries at their first
// occurrence (the strategy of ESBMC's emit_ast): bindings accumulate in
// Prefix in dependency order and the matching closing parens are appended
// at the end. Once-used subterms are inlined, so tree-shaped formulas are
// emitted exactly as before, without lets.
class SMTLIBRenderer {
public:
  std::string render(const SMTExpr &Root) {
    countRefs(Root);
    std::string Body = emit(Root);
    if (OpenLets == 0)
      return Body;
    std::string Out = std::move(Prefix);
    Out += Body;
    Out.append(OpenLets, ')');
    return Out;
  }

private:
  static const SMTLIBTerm &termOf(const SMTExpr &E) {
    return toSolverExpr<SMTLIBExpr>(E).Expr;
  }

  void countRefs(const SMTExpr &Root) {
    std::vector<const SMTExpr *> Stack{&Root};
    while (!Stack.empty()) {
      const SMTExpr *E = Stack.back();
      Stack.pop_back();
      if (++RefCount[E] > 1)
        continue;
      const SMTLIBTerm &T = termOf(*E);
      if (T.OwnScope)
        continue; // binder args render in their own scope
      for (const SMTExprRef &Arg : T.Args)
        Stack.push_back(&*Arg);
    }
  }

  // Iterative post-order emission: recursion would overflow the stack on
  // deep, lightly shared chains (SSA-style formulas reach hundreds of
  // thousands of nodes).
  std::string emit(const SMTExpr &Root) {
    struct Frame {
      const SMTExpr *E;
      const SMTLIBTerm *T;
      std::size_t NextArg;
      std::string Text;
    };
    std::string Leaf;
    std::vector<Frame> Stack;
    // Returns true when the expression's text is available immediately in
    // Leaf (terminal or memoized); otherwise opens a frame for it.
    const auto enter = [&](const SMTExpr &E) {
      const SMTLIBTerm &T = termOf(E);
      if (T.Args.empty()) {
        Leaf = T.Head; // terminals are cheap: always inline
        return true;
      }
      if (auto It = Memo.find(&E); It != Memo.end()) {
        Leaf = It->second;
        return true;
      }
      Stack.push_back(Frame{&E, &T, 0, "(" + T.Head});
      return false;
    };
    if (enter(Root))
      return Leaf;
    while (true) {
      Frame &F = Stack.back();
      if (F.NextArg < F.T->Args.size()) {
        const SMTExprRef &Arg = F.T->Args[F.NextArg];
        F.Text += " ";
        ++F.NextArg;
        // Binder arguments must not share subterms with the outside of the
        // binder, so they render in a fresh scope. Inner let temporaries
        // may shadow outer ones; that is harmless because a fresh scope
        // never references outer temporaries.
        if (F.T->OwnScope) {
          F.Text += SMTLIBRenderer().render(*Arg);
          continue;
        }
        if (enter(*Arg))
          Stack.back().Text += Leaf; // enter() may have re-seated back()
        continue;
      }
      F.Text += ")";
      std::string Done = std::move(F.Text);
      const SMTExpr *E = F.E;
      Stack.pop_back();
      if (RefCount[E] > 1) {
        // Temp names contain a bare '%', which quoteSymbol output can never
        // produce (every literal '%' in a user name is encoded as "%25"),
        // so a temporary can never capture a user symbol.
        std::string Temp = "%t" + std::to_string(NextTemp++);
        Prefix += "(let ((" + Temp + " " + Done + ")) ";
        ++OpenLets;
        Memo.emplace(E, Temp);
        Done = std::move(Temp);
      }
      if (Stack.empty())
        return Done;
      Stack.back().Text += Done;
    }
  }

  std::unordered_map<const SMTExpr *, unsigned> RefCount;
  std::unordered_map<const SMTExpr *, std::string> Memo;
  std::string Prefix;
  unsigned OpenLets = 0;
  unsigned NextTemp = 0;
};

std::string renderSMTLIBExpr(const SMTExpr &E) {
  return SMTLIBRenderer().render(E);
}

std::string renderSMTLIBExpr(const SMTExprRef &E) {
  return SMTLIBRenderer().render(*E);
}

} // namespace

// ---------------------------------------------------------------------------
// SMTLIBSort / SMTLIBExpr
// ---------------------------------------------------------------------------

unsigned SMTLIBSort::getWidthFromSolver() const {
  // We do not have an external solver to consult; the stored width *is* the
  // truth. Return the stored payload directly. validateSortWidth() short-
  // circuits for array/function/tuple/arith sorts, so this method is only
  // ever called for kinds where getStoredWidth() succeeds (BV, FP, BVFP, RM,
  // BVRM, Bool). For FP sorts in particular the stored Width already reflects
  // the encoded representation; do not re-derive it from sig/exp here, since
  // BVFP stores SigWidth as the *encoded* significand width.
  return getStoredWidth();
}

void SMTLIBSort::dump() const {
  std::string Out;
  dump(Out);
  std::fprintf(stderr, "%s", Out.c_str());
}

void SMTLIBSort::dump(std::string &Out) const {
  Out = Sort;
  Out += "\n";
}

bool SMTLIBExpr::equal_to(SMTExpr const &Other) const {
  if (Sort != Other.Sort || Other.getBackendKind() != getBackendKind())
    return false;
  const auto &O = static_cast<const SMTLIBExpr &>(Other);
  if (Expr.Head != O.Expr.Head || Expr.OwnScope != O.Expr.OwnScope ||
      Expr.Args.size() != O.Expr.Args.size())
    return false;
  for (std::size_t I = 0; I < Expr.Args.size(); ++I)
    if (&*Expr.Args[I] != &*O.Expr.Args[I] &&
        !(*Expr.Args[I] == *O.Expr.Args[I]))
      return false;
  return true;
}

void SMTLIBExpr::dump() const {
  std::string Out;
  dump(Out);
  std::fprintf(stderr, "%s", Out.c_str());
}

void SMTLIBExpr::dump(std::string &Out) const {
  Out = renderSMTLIBExpr(*this);
  Out += "\n";
}

// ---------------------------------------------------------------------------
// FileEmitter
// ---------------------------------------------------------------------------

FileEmitter::FileEmitter(const std::string &Path) {
  if (Path.empty())
    return;
  if (Path == "-") {
    Out = stdout;
    OwnsHandle = false;
    return;
  }
  Out = std::fopen(Path.c_str(), "w");
  fatalErrorIf(Out == nullptr, "FileEmitter could not open output file");
  OwnsHandle = true;
}

FileEmitter::~FileEmitter() noexcept {
  if (Out && OwnsHandle)
    std::fclose(Out);
}

void FileEmitter::emitRaw(const std::string &Text) const {
  if (!Out)
    return;
  std::fwrite(Text.data(), 1, Text.size(), Out);
}

void FileEmitter::flush() const {
  if (Out)
    std::fflush(Out);
}

// ---------------------------------------------------------------------------
// ProcessEmitter
// ---------------------------------------------------------------------------

namespace {

// Read one SMT-LIB response from the given stream. Returns the text with
// surrounding whitespace trimmed. Handles three shapes:
//   - bare token line: `success`, `sat`, `unsat`, `unknown`, or numbers
//   - parenthesized: `((<symbol> <value>))` — read until parens balance,
//     respecting `|...|` quoted symbols and `"..."` string literals
//   - error: `(error "...")` — same parens-balanced shape
//
// Returns the empty string on EOF.
std::string readOneSmtlibResponse(std::FILE *In) {
  fatalErrorIf(!In, "ProcessEmitter::readResponse: stream is null");

  // Skip leading whitespace.
  int C;
  do {
    C = std::fgetc(In);
    if (C == EOF)
      return {};
  } while (C == ' ' || C == '\t' || C == '\n' || C == '\r');

  std::string Out;
  if (C != '(') {
    // Bare token: read until whitespace or EOF.
    Out.push_back(static_cast<char>(C));
    while ((C = std::fgetc(In)) != EOF && C != '\n' && C != '\r' && C != ' ' &&
           C != '\t')
      Out.push_back(static_cast<char>(C));
    return Out;
  }

  // Parenthesized: balance parens, with `|...|` and `"..."` awareness.
  Out.push_back('(');
  int Depth = 1;
  bool InQuoted = false; // inside |...|
  bool InString = false; // inside "..."
  while (Depth > 0) {
    C = std::fgetc(In);
    if (C == EOF)
      return Out; // child died mid-response; let the caller deal with it
    char Ch = static_cast<char>(C);
    Out.push_back(Ch);
    if (InQuoted) {
      if (Ch == '|')
        InQuoted = false;
      continue;
    }
    if (InString) {
      if (Ch == '"')
        InString = false;
      continue;
    }
    if (Ch == '|')
      InQuoted = true;
    else if (Ch == '"')
      InString = true;
    else if (Ch == '(')
      ++Depth;
    else if (Ch == ')')
      --Depth;
  }
  return Out;
}

} // namespace

namespace {

// Open a pipe with both ends marked CLOEXEC. Uses pipe2(O_CLOEXEC) on
// Linux; on platforms without pipe2 (notably macOS), falls back to pipe()
// + fcntl(F_SETFD, FD_CLOEXEC). Returns 0 on success, -1 on failure.
//
// The pipe()/fcntl() fallback has a small race window where another
// thread could fork+exec and inherit the FDs. SMTLIBSolver constructs
// happen on the calling thread before any solver fork, so the window is
// closed in practice; documenting the trade-off rather than working
// around it (the alternative is platform-specific posix_spawn plumbing).
inline int openPipeCloexec(int Fds[2]) {
#ifdef O_CLOEXEC
#if defined(__linux__) || defined(__GLIBC__)
  return ::pipe2(Fds, O_CLOEXEC);
#endif
#endif
  if (::pipe(Fds) != 0)
    return -1;
  for (int I = 0; I < 2; ++I) {
    int Flags = ::fcntl(Fds[I], F_GETFD);
    if (Flags < 0 || ::fcntl(Fds[I], F_SETFD, Flags | FD_CLOEXEC) < 0) {
      ::close(Fds[0]);
      ::close(Fds[1]);
      return -1;
    }
  }
  return 0;
}

// Async-signal-safe child-side abort: write a fixed message to
// STDERR_FILENO (best-effort; we're about to exit anyway), then _Exit.
// Must be used in the post-fork pre-exec window instead of fatalErrorIf,
// which uses fprintf and is not async-signal-safe.
[[noreturn]] inline void childAbort(const char *Msg, size_t Len) {
  ssize_t Ignored = ::write(STDERR_FILENO, Msg, Len);
  (void)Ignored;
  std::_Exit(127);
}

#define CAMADA_CHILD_ABORT(msg) childAbort((msg), sizeof(msg) - 1)

// Move `Fd` to a fresh fd >= 3 with CLOEXEC set, so the subsequent dup2
// onto stdin/stdout/stderr is guaranteed to be a real copy (which clears
// CLOEXEC on the destination). If the host has closed standard descriptors
// before constructing SMTLIBSolver, pipe2 can hand back FDs at 0/1/2; a
// dup2(0, 0) is a no-op that leaves CLOEXEC set, so the kernel would close
// the wired stdio on exec.
//
// Closes the original FD on success; the caller continues with `Fd`
// updated. On F_DUPFD_CLOEXEC failure (e.g. an extremely tight RLIMIT
// where pipe2 already exhausted the table), uses the async-signal-safe
// child-abort path — fatalErrorIf would deadlock under fork.
inline void renumberAboveStdio(int &Fd) {
  if (Fd >= 3)
    return;
  int New = ::fcntl(Fd, F_DUPFD_CLOEXEC, 3);
  if (New < 0)
    CAMADA_CHILD_ABORT("ProcessEmitter: F_DUPFD_CLOEXEC failed\n");
  ::close(Fd);
  Fd = New;
}

// Compute a safe upper bound for the fd table in the *parent*, before
// fork. Used by the post-fork close-loop fallback so the child never has
// to call sysconf()/getrlimit() (neither is guaranteed async-signal-safe
// in a multithreaded host: the child inherits only the calling thread,
// so any libc lock held by another thread at fork would deadlock).
//
// Honors the actual RLIMIT_NOFILE — silently capping to 1024 when sysconf
// reports a higher limit would leak high-numbered non-CLOEXEC FDs into
// the solver. We only fall back to 1024 if both getrlimit and sysconf
// fail to report a usable value.
inline int computeFdLimitForChild() {
  struct rlimit Rl;
  if (::getrlimit(RLIMIT_NOFILE, &Rl) == 0 && Rl.rlim_cur != RLIM_INFINITY &&
      Rl.rlim_cur > 0) {
    rlim_t V = Rl.rlim_cur;
    if (V > static_cast<rlim_t>(INT_MAX))
      V = static_cast<rlim_t>(INT_MAX);
    return static_cast<int>(V);
  }
  long Max = ::sysconf(_SC_OPEN_MAX);
  if (Max > 0) {
    if (Max > INT_MAX)
      Max = INT_MAX;
    return static_cast<int>(Max);
  }
  return 1024;
}

// Close every fd above STDERR_FILENO in the calling process. ASYNC-SIGNAL-
// SAFE: callable in the post-fork pre-exec window of a forked child. Only
// uses close_range and close(); no malloc/dirent/sysconf/stdio. The
// `MaxFd` upper bound must be computed in the parent before fork.
//
// LINUX ONLY. macOS depends on inherited fds for launchd/bootstrap-port
// IPC inside libSystem; closing them blocks dyld from loading any
// dynamically-linked binary in the child. Our pipes are already created
// with FD_CLOEXEC, which is the only descriptor hygiene Camada itself
// owns. Host-process fd hygiene (the trust-boundary concern Codex raised)
// is Linux-only here; macOS users that need it should use posix_spawn
// with POSIX_SPAWN_CLOEXEC_DEFAULT in their integration layer.
//
// On Linux, tries close_range first (5.9+); falls back to a bounded
// close() loop for older kernels. Belt-and-suspenders for host-process
// FDs that weren't opened with CLOEXEC.
inline void closeFdsAboveStderr([[maybe_unused]] int MaxFd) {
#if defined(__linux__)
#ifdef SYS_close_range
  long Rc = ::syscall(SYS_close_range, STDERR_FILENO + 1, ~0U, 0);
  if (Rc == 0)
    return;
#endif
  for (int Fd = STDERR_FILENO + 1; Fd < MaxFd; ++Fd)
    ::close(Fd);
#endif
}

// Shared fork + pipe + wire-stdio scaffolding. The caller provides an
// `ExecInChild` callback that runs in the forked child after stdin/stdout/
// stderr have been wired to the pipes; it must call exec*() and never
// return on success. Returns the child PID and populates In/Out with the
// parent-side ends of the pipes. Aborts via fatalErrorIf on any setup
// failure.
//
// FD hygiene:
//   - Pipes are opened with pipe2(O_CLOEXEC). For host-process FDs that
//     are NOT CLOEXEC, the child also closes everything above STDERR via
//     close_range (or a bounded close() loop) just before exec.
//   - In the child, pipe endpoints are renumbered above STDERR before
//     being dup2'd onto stdin/stdout/stderr. This guarantees dup2's
//     `src != dst` invariant and therefore the CLOEXEC-clearing semantics
//     it provides on the destination FD. Without that step, a host that
//     closed stdin/stdout could see pipe2 reuse fd 0/1, and dup2(0, 0)
//     would be a no-op leaving CLOEXEC set — execvp would then close the
//     solver's own stdio.
//   - Everything between fork() and exec*() is async-signal-safe: only
//     close_range/close/dup2/fcntl. No malloc, dirent walking, stdio, or
//     sysconf. In a multithreaded host the child inherits only the forking
//     thread; any libc lock held by another thread at fork would deadlock
//     the child if we touched the corresponding subsystem.
template <typename ExecInChild>
long forkAndWire(std::FILE *&In, std::FILE *&Out, ExecInChild ExecInChildFn) {
  int InPipe[2];  // child stdout -> parent reads
  int OutPipe[2]; // parent writes -> child stdin
  fatalErrorIf(openPipeCloexec(InPipe) != 0,
               "ProcessEmitter: failed to open pipe");
  fatalErrorIf(openPipeCloexec(OutPipe) != 0,
               "ProcessEmitter: failed to open pipe");

  // Compute the fd-table limit BEFORE fork; the child must not call
  // sysconf() in its post-fork pre-exec window.
  const int MaxFd = computeFdLimitForChild();

  pid_t Child = ::fork();
  fatalErrorIf(Child < 0, "ProcessEmitter: fork() failed");

  if (Child == 0) {
    // Child: move every pipe endpoint we'll use to fd >= 3 first, so the
    // subsequent dup2 calls are real copies (which clear CLOEXEC on the
    // destination). dup2(N, N) is a no-op and would leave CLOEXEC set,
    // closing the wired stdio across exec.
    int ChildIn = OutPipe[0];
    int ChildOut = InPipe[1];
    renumberAboveStdio(ChildIn);
    renumberAboveStdio(ChildOut);

    if (::dup2(ChildIn, STDIN_FILENO) < 0)
      CAMADA_CHILD_ABORT("ProcessEmitter: dup2(stdin) failed\n");
    if (::dup2(ChildOut, STDOUT_FILENO) < 0)
      CAMADA_CHILD_ABORT("ProcessEmitter: dup2(stdout) failed\n");
    if (::dup2(ChildOut, STDERR_FILENO) < 0)
      CAMADA_CHILD_ABORT("ProcessEmitter: dup2(stderr) failed\n");

    // Close every other fd before exec. Pipes opened with CLOEXEC are
    // already covered, but host-process FDs without CLOEXEC would
    // otherwise be inherited by the solver process.
    closeFdsAboveStderr(MaxFd);

    ExecInChildFn();
    std::_Exit(127);
  }

  // Parent: close the ends we don't own. Their CLOEXEC bit was set by
  // pipe2, so even if we somehow leaked them they'd be cleaned up across
  // any subsequent exec on this side.
  ::close(OutPipe[0]);
  ::close(InPipe[1]);
  Out = ::fdopen(OutPipe[1], "w");
  In = ::fdopen(InPipe[0], "r");
  fatalErrorIf(Out == nullptr || In == nullptr,
               "ProcessEmitter: fdopen() failed on pipe ends");
  // Disable stdio's read-buffering on the input stream. We use fgetc to
  // parse responses byte-by-byte, but we ALSO want select()-based polling
  // (in drainResponses) to accurately report whether more data is available.
  // With a stdio read buffer in the way, fgetc may have already pulled
  // bytes into libc, leaving select() unable to see them. Unbuffered
  // reads keep stdio and the kernel pipe in sync.
  ::setvbuf(In, nullptr, _IONBF, 0);
  return static_cast<long>(Child);
}

// Install SIGPIPE=SIG_IGN exactly once for the lifetime of the host process,
// the first time any ProcessEmitter is constructed. Per-instance restore
// would race destructively when multiple SMTLIBSolver instances coexist:
// destroying one would reinstate the previous handler while the other is
// still writing to its child, and a later EPIPE would kill the host. The
// "install once, never restore" idiom is what mainstream libraries that
// drive subprocesses already do (curl, ssh, etc.); host applications that
// require a different policy will reinstall their own handler regardless,
// and this code only ever clobbers SIGPIPE the first time.
//
// std::call_once + a mutex would be cleaner, but Camada otherwise stays
// out of <thread>, so use the equivalent atomic flag.
void ensureSigpipeIgnored() {
  static std::atomic<bool> Installed{false};
  bool Expected = false;
  if (Installed.compare_exchange_strong(Expected, true)) {
    using Handler = void (*)(int);
    Handler Prev = std::signal(SIGPIPE, SIG_IGN);
    fatalErrorIf(Prev == SIG_ERR,
                 "ProcessEmitter: failed to install SIGPIPE handler");
    (void)Prev; // intentionally not stored — see comment above.
  }
}

} // namespace

ProcessEmitter::ProcessEmitter(const std::vector<std::string> &Argv) {
  fatalErrorIf(Argv.empty(),
               "SMTLIBSolver: ProcessEmitter requires a non-empty argv");
  fatalErrorIf(Argv[0].empty(),
               "SMTLIBSolver: ProcessEmitter argv[0] must be non-empty");

  // Build a NULL-terminated argv suitable for execvp. We materialize the
  // pointer array in the parent; it's safe to pass through fork/exec
  // because fork preserves the address space until the child execs.
  std::vector<char *> ArgvPtrs;
  ArgvPtrs.reserve(Argv.size() + 1);
  for (const auto &A : Argv)
    ArgvPtrs.push_back(const_cast<char *>(A.c_str()));
  ArgvPtrs.push_back(nullptr);

  ensureSigpipeIgnored();
  Pid = forkAndWire(In, Out,
                    [&ArgvPtrs]() { ::execvp(ArgvPtrs[0], ArgvPtrs.data()); });
}

ProcessEmitter::~ProcessEmitter() noexcept {
  if (Out)
    std::fclose(Out);
  if (In)
    std::fclose(In);
  if (Pid > 0) {
    ::kill(static_cast<pid_t>(Pid), SIGTERM);
    int Status = 0;
    ::waitpid(static_cast<pid_t>(Pid), &Status, 0);
  }
}

void ProcessEmitter::emitRaw(const std::string &Text) const {
  if (!Out)
    return;
  std::fwrite(Text.data(), 1, Text.size(), Out);
}

void ProcessEmitter::flush() const {
  if (Out)
    std::fflush(Out);
}

std::string ProcessEmitter::readResponse() const {
  return readOneSmtlibResponse(In);
}

unsigned ProcessEmitter::drainResponses(unsigned TimeoutMs) const {
  if (!In)
    return 0;
  unsigned Drained = 0;
  // Loop: poll the FD with select(); if data is available within the timeout,
  // read one response and try again.
  //
  // Caveat: readOneSmtlibResponse uses fgetc which fills a stdio buffer, and
  // select() only sees the underlying FD. We work around this by calling
  // fflush(In) before the select to make stdio's notion of "buffered data"
  // and the kernel's notion of "ready FD" line up — fflush on an input
  // stream is implementation-defined, but on glibc it discards any buffered-
  // but-unread bytes, forcing the next fgetc to actually read from the FD.
  int Fd = ::fileno(In);
  while (true) {
    fd_set ReadFds;
    FD_ZERO(&ReadFds);
    FD_SET(Fd, &ReadFds);
    struct timeval Timeout;
    Timeout.tv_sec = TimeoutMs / 1000;
    Timeout.tv_usec = (TimeoutMs % 1000) * 1000;
    int Ready = ::select(Fd + 1, &ReadFds, nullptr, nullptr, &Timeout);
    if (Ready <= 0)
      break; // no more responses pending within the timeout
    (void)readOneSmtlibResponse(In);
    ++Drained;
  }
  return Drained;
}

// ---------------------------------------------------------------------------
// SMTLIBSolver
// ---------------------------------------------------------------------------

namespace {

// Helper: format an unsigned width into a decimal string.
std::string utoa(unsigned V) { return std::to_string(V); }

// Convert a Camada user-supplied symbol name into a quoted SMT-LIB symbol.
//
// We unconditionally wrap in vertical bars to side-step the SMT-LIB simple-
// symbol grammar (which forbids characters like `:` and `.` that ESBMC
// produces in names like `main::1::faces.a`).
//
// The two characters forbidden *inside* a `|...|` quoted symbol are `|` and
// `\`. We percent-encode them (and `%` itself, to keep the encoding
// reversible and collision-free): `|` -> `%7C`, `\` -> `%5C`, `%` -> `%25`.
// This guarantees every distinct Camada name maps to a distinct SMT-LIB
// symbol, so two different callers can never alias each other's
// declarations.
std::string quoteSymbol(const std::string &Name) {
  std::string Out;
  Out.reserve(Name.size() + 2);
  Out.push_back('|');
  for (char C : Name) {
    switch (C) {
    case '%':
      Out.append("%25");
      break;
    case '|':
      Out.append("%7C");
      break;
    case '\\':
      Out.append("%5C");
      break;
    default:
      Out.push_back(C);
      break;
    }
  }
  Out.push_back('|');
  return Out;
}

const std::string &textOf(const SMTSortRef &S) {
  return toSolverSort<SMTLIBSort>(*S).Sort;
}

} // namespace

SMTLIBSolver::SMTLIBSolver(const std::string &OutputPath,
                           TupleEncoding TupleMode)
    : File(std::make_unique<FileEmitter>(OutputPath)), TupleMode(TupleMode) {
  emitPreamble();
  initializeCommonSingletons();
}

SMTLIBSolver::SMTLIBSolver(SMTLIBProcessTag,
                           const std::vector<std::string> &Argv,
                           TupleEncoding TupleMode)
    : Proc(std::make_unique<ProcessEmitter>(Argv)), TupleMode(TupleMode) {
  emitPreamble();
  initializeCommonSingletons();
}

SMTLIBSolver::SMTLIBSolver(SMTLIBProcessTag,
                           const std::vector<std::string> &Argv,
                           const std::string &OutputPath,
                           TupleEncoding TupleMode)
    : File(std::make_unique<FileEmitter>(OutputPath)),
      Proc(std::make_unique<ProcessEmitter>(Argv)), TupleMode(TupleMode) {
  emitPreamble();
  initializeCommonSingletons();
}

SMTLIBSolver::~SMTLIBSolver() { invalidateGeneratedObjects(); }

void SMTLIBSolver::emitPreamble() {
  // Interactive mode: the very first emitted command is
  // `(set-option :print-success true)`. Standard-conforming SMT-LIB solvers
  // (z3, cvc5) acknowledge that command itself with `success`, so emitLine's
  // ack-on-every-line regime works from the start. Write-only mode emits
  // `:print-success false` to keep captured scripts terse for offline replay.
  if (Proc)
    emitLine("(set-option :print-success true)");
  else if (File)
    File->emitRaw("(set-option :print-success false)\n");

  // cvc5 and bitwuzla refuse (get-value ...) unless model production is
  // explicitly enabled; z3 and yices-smt2 default to producing models. Set
  // the option unconditionally for protocol portability.
  emitLine("(set-option :produce-models true)");
  // Needed for (get-unsat-assumptions). Unlike the options above, not every
  // child implements it, and the standard reply for an unimplemented option
  // is `unsupported` — not an error — so this one bypasses emitLine's
  // success-or-die handling and records the answer instead.
  const std::string UnsatAssumptionsOpt =
      "(set-option :produce-unsat-assumptions true)\n";
  if (File)
    File->emitRaw(UnsatAssumptionsOpt);
  if (Proc) {
    Proc->emitRaw(UnsatAssumptionsOpt);
    Proc->flush();
    UnsatAssumptionsSupported = Proc->readResponse() == "success";
  }
  // Without :global-declarations true, declarations made inside a (push) are
  // discarded on (pop). Camada's API lets a caller mkSymbol() inside a pushed
  // scope and use the returned expression after pop(); without this option,
  // the next (assert ...) or (get-value ...) referring to that symbol would
  // hit "unknown constant" in the child solver. All solvers in the verified
  // matrix accept this option.
  emitLine("(set-option :global-declarations true)");
  emitLine("(set-info :status unknown)");
  // ALL covers BV/Bool/arrays/FP/Int/Real, which is the full Camada
  // surface. Children that don't support a particular sort will reject the
  // first command that uses it (yices-smt2 has no FP, for example). Callers
  // who want a portable script across heterogeneous solvers should pick
  // FPEncoding::BV at sort-construction time — that already routes every FP
  // op through the common-layer bit-blast path.
  emitLine("(set-logic ALL)");
}

void SMTLIBSolver::emitLine(const std::string &Text) const {
  const std::string Line = Text + "\n";
  if (File)
    File->emitRaw(Line);
  if (Proc) {
    Proc->emitRaw(Line);
    Proc->flush();
    // Discard the `success` ack. If the child returned `(error "...")`, abort
    // with the message — there's no recovery from a malformed command in this
    // simple synchronous protocol.
    std::string Resp = Proc->readResponse();
    if (Resp != "success")
      fatalErrorIf(true,
                   ("SMTLIBSolver: child solver returned: " + Resp).c_str());
  }
}

SMTExprRef SMTLIBSolver::makeSMTLIBExpr(SMTExprKind Kind,
                                        const SMTSortRef &Sort,
                                        std::string Text) {
  return makeExprRef<SMTLIBExpr>(Kind, this, Sort,
                                 SMTLIBTerm{std::move(Text), {}, false});
}

SMTExprRef SMTLIBSolver::makeSMTLIBExpr(SMTExprKind Kind,
                                        const SMTSortRef &Sort,
                                        std::string Head,
                                        std::vector<SMTExprRef> Args,
                                        bool OwnScope) {
  return makeExprRef<SMTLIBExpr>(
      Kind, this, Sort, SMTLIBTerm{std::move(Head), std::move(Args), OwnScope});
}

// --- core dispatch helpers ---

SMTExprRef SMTLIBSolver::rewrapExprImpl(const SMTExpr &Exp,
                                        const SMTSortRef &Sort,
                                        SMTExprKind Kind) {
  const auto &E = toSolverExpr<SMTLIBExpr>(Exp);
  return makeExprRef<SMTLIBExpr>(Kind, E.Context, Sort, E.Expr);
}

void SMTLIBSolver::addConstraintImpl(const SMTExprRef &Exp) {
  emitLine("(assert " + renderSMTLIBExpr(Exp) + ")");
}

// --- sorts ---

SMTSortRef SMTLIBSolver::mkBoolSortImpl() {
  return makeSortRef<SMTLIBSort>(
      SMTLIBSort(SMTSortKind::Bool, this, "Bool", SMTSort::ScalarSortData{1}));
}

SMTSortRef SMTLIBSolver::mkBVSortImpl(unsigned BitWidth) {
  return makeSortRef<SMTLIBSort>(SMTLIBSort(SMTSortKind::BV, this,
                                            "(_ BitVec " + utoa(BitWidth) + ")",
                                            SMTSort::ScalarSortData{BitWidth}));
}

SMTSortRef SMTLIBSolver::mkBVFPSortImpl(unsigned ExpWidth, unsigned SigWidth) {
  unsigned Width = ExpWidth + SigWidth + 1;
  return makeSortRef<SMTLIBSort>(
      SMTLIBSort(SMTSortKind::BVFP, this, "(_ BitVec " + utoa(Width) + ")",
                 SMTSort::FPSortData{Width, ExpWidth, SigWidth + 1}));
}

SMTSortRef SMTLIBSolver::mkBVRMSortImpl() {
  return makeSortRef<SMTLIBSort>(SMTLIBSort(
      SMTSortKind::BVRM, this, "(_ BitVec 3)", SMTSort::ScalarSortData{3}));
}

// Native FP. Camada's API takes SigWidth excluding the hidden bit (matches the
// CVC5 backend's convention: mkFPSortImpl(8, 23) → 32-bit FP). SMT-LIB's
// (_ FloatingPoint eb sb) counts the hidden bit, so we emit sb+1.
SMTSortRef SMTLIBSolver::mkFPSortImpl(unsigned ExpWidth, unsigned SigWidth) {
  unsigned Width = ExpWidth + SigWidth + 1;
  std::string Text =
      "(_ FloatingPoint " + utoa(ExpWidth) + " " + utoa(SigWidth + 1) + ")";
  return makeSortRef<SMTLIBSort>(
      SMTLIBSort(SMTSortKind::FP, this, std::move(Text),
                 SMTSort::FPSortData{Width, ExpWidth, SigWidth}));
}

SMTSortRef SMTLIBSolver::mkRMSortImpl() {
  return makeSortRef<SMTLIBSort>(SMTLIBSort(
      SMTSortKind::RM, this, "RoundingMode", SMTSort::ScalarSortData{3}));
}

SMTSortRef SMTLIBSolver::mkIntSortImpl() {
  return makeSortRef<SMTLIBSort>(SMTLIBSort(SMTSortKind::Int, this, "Int"));
}

SMTSortRef SMTLIBSolver::mkRealSortImpl() {
  return makeSortRef<SMTLIBSort>(SMTLIBSort(SMTSortKind::Real, this, "Real"));
}

// Function sort. SMT-LIB has no first-class function-sort syntax to put on
// the wire — function sorts only appear in (declare-fun name (D1 ...) Cod).
// We still need a SortRef the rest of Camada can carry around, so emit a
// placeholder text that is never spliced into wire output. mkSymbolImpl
// destructures the FunctionSortData when emitting the actual declaration.
SMTSortRef
SMTLIBSolver::mkFunctionSortImpl(const std::vector<SMTSortRef> &DomainSorts,
                                 const SMTSortRef &CodomainSort) {
  std::string Text = "(";
  for (std::size_t I = 0; I < DomainSorts.size(); ++I) {
    if (I)
      Text += " ";
    Text += textOf(DomainSorts[I]);
  }
  Text += ") ";
  Text += textOf(CodomainSort);
  return makeSortRef<SMTLIBSort>(
      SMTLIBSort(SMTSortKind::Function, this, std::move(Text),
                 SMTSort::FunctionSortData{DomainSorts, CodomainSort}));
}

// Tuple sort via SMT-LIB declare-datatypes. Eagerly emit a fresh datatype
// declaration whose constructor and projector names are derived from the
// fresh sort name: `__camada_tup<N>` for the sort, `__camada_tup<N>_mk` for
// the constructor, `__camada_tup<N>_p<i>` for projector i. Camada caches
// tuple sorts by element identity, so this runs at most once per distinct
// shape — no risk of redefining a datatype.
//
// Only z3 and cvc5 in the verified matrix support `declare-datatypes`;
// bitwuzla, mathsat, and yices-smt2 reject the command. Callers using those
// children with tuples will get the child's `error`/`unsupported` reply,
// which surfaces through emitLine's standard error path.
SMTSortRef
SMTLIBSolver::mkTupleSortImpl(const std::vector<SMTSortRef> &ElementSorts) {
  std::string Name = "__camada_tup" + utoa(NextTupleId++);
  const std::string Prefix = Name + "_p";
  std::string Decl = "(declare-datatypes ((" + Name + " 0)) (((" + Name + "_mk";
  for (std::size_t I = 0; I < ElementSorts.size(); ++I) {
    Decl += " (";
    Decl += Prefix;
    Decl += utoa(I);
    Decl += " ";
    Decl += textOf(ElementSorts[I]);
    Decl += ")";
  }
  Decl += "))))";
  emitLine(Decl);
  return makeSortRef<SMTLIBSort>(
      SMTLIBSort(SMTSortKind::Tuple, this, std::move(Name),
                 SMTSort::TupleSortData{ElementSorts}));
}

SMTSortRef SMTLIBSolver::mkArraySortImpl(const SMTSortRef &IndexSort,
                                         const SMTSortRef &ElemSort) {
  std::string Text =
      "(Array " + textOf(IndexSort) + " " + textOf(ElemSort) + ")";
  return makeSortRef<SMTLIBSort>(
      SMTLIBSort(SMTSortKind::Array, this, std::move(Text),
                 SMTSort::ArraySortData{IndexSort, ElemSort}));
}

// --- straight-line expression builders ---

#define CAMADA_SMTLIB_UNARY(Name, OpStr, Kind, ResultSort)                     \
  SMTExprRef SMTLIBSolver::Name(const SMTExprRef &Exp) {                       \
    return makeSMTLIBExpr(SMTExprKind::Kind, ResultSort, OpStr, {Exp});        \
  }

#define CAMADA_SMTLIB_BINARY(Name, OpStr, Kind, ResultSort)                    \
  SMTExprRef SMTLIBSolver::Name(const SMTExprRef &LHS,                         \
                                const SMTExprRef &RHS) {                       \
    return makeSMTLIBExpr(SMTExprKind::Kind, ResultSort, OpStr, {LHS, RHS});   \
  }

// Rounded binary FP arithmetic: (op rm lhs rhs).
#define CAMADA_SMTLIB_RM_BINARY(Name, OpStr, Kind)                             \
  SMTExprRef SMTLIBSolver::Name(const SMTExprRef &LHS, const SMTExprRef &RHS,  \
                                const SMTExprRef &R) {                         \
    return makeSMTLIBExpr(SMTExprKind::Kind, LHS->Sort, OpStr, {R, LHS, RHS}); \
  }

CAMADA_SMTLIB_UNARY(mkBVNegImpl, "bvneg", BVNeg, Exp->Sort)
CAMADA_SMTLIB_UNARY(mkBVNotImpl, "bvnot", BVNot, Exp->Sort)
CAMADA_SMTLIB_UNARY(mkNotImpl, "not", Not, Exp->Sort)

CAMADA_SMTLIB_BINARY(mkBVAddImpl, "bvadd", BVAdd, LHS->Sort)
CAMADA_SMTLIB_BINARY(mkBVSubImpl, "bvsub", BVSub, LHS->Sort)
CAMADA_SMTLIB_BINARY(mkBVMulImpl, "bvmul", BVMul, LHS->Sort)
CAMADA_SMTLIB_BINARY(mkBVSRemImpl, "bvsrem", BVSRem, LHS->Sort)
CAMADA_SMTLIB_BINARY(mkBVURemImpl, "bvurem", BVURem, LHS->Sort)
CAMADA_SMTLIB_BINARY(mkBVSDivImpl, "bvsdiv", BVSDiv, LHS->Sort)
CAMADA_SMTLIB_BINARY(mkBVUDivImpl, "bvudiv", BVUDiv, LHS->Sort)
CAMADA_SMTLIB_BINARY(mkBVShlImpl, "bvshl", BVShl, LHS->Sort)
CAMADA_SMTLIB_BINARY(mkBVAshrImpl, "bvashr", BVAshr, LHS->Sort)
CAMADA_SMTLIB_BINARY(mkBVLshrImpl, "bvlshr", BVLshr, LHS->Sort)
CAMADA_SMTLIB_BINARY(mkBVXorImpl, "bvxor", BVXor, LHS->Sort)
CAMADA_SMTLIB_BINARY(mkBVOrImpl, "bvor", BVOr, LHS->Sort)
CAMADA_SMTLIB_BINARY(mkBVAndImpl, "bvand", BVAnd, LHS->Sort)
CAMADA_SMTLIB_BINARY(mkBVUltImpl, "bvult", BVUlt, mkBoolSort())
CAMADA_SMTLIB_BINARY(mkBVSltImpl, "bvslt", BVSlt, mkBoolSort())
CAMADA_SMTLIB_BINARY(mkBVUleImpl, "bvule", BVUle, mkBoolSort())
CAMADA_SMTLIB_BINARY(mkBVSleImpl, "bvsle", BVSle, mkBoolSort())
CAMADA_SMTLIB_BINARY(mkEqualImpl, "=", Equal, mkBoolSort())
CAMADA_SMTLIB_BINARY(mkAndImpl, "and", And, mkBoolSort())
CAMADA_SMTLIB_BINARY(mkOrImpl, "or", Or, mkBoolSort())

SMTExprRef SMTLIBSolver::mkIteImpl(const SMTExprRef &Cond, const SMTExprRef &T,
                                   const SMTExprRef &F) {
  return makeSMTLIBExpr(SMTExprKind::Ite, T->Sort, "ite", {Cond, T, F});
}

SMTExprRef SMTLIBSolver::mkBVSignExtImpl(unsigned i, const SMTExprRef &Exp) {
  unsigned NewWidth = Exp->getWidth() + i;
  return makeSMTLIBExpr(SMTExprKind::BVSignExt, mkBVSort(NewWidth),
                        "(_ sign_extend " + utoa(i) + ")", {Exp});
}

SMTExprRef SMTLIBSolver::mkBVZeroExtImpl(unsigned i, const SMTExprRef &Exp) {
  unsigned NewWidth = Exp->getWidth() + i;
  return makeSMTLIBExpr(SMTExprKind::BVZeroExt, mkBVSort(NewWidth),
                        "(_ zero_extend " + utoa(i) + ")", {Exp});
}

SMTExprRef SMTLIBSolver::mkBVExtractImpl(unsigned High, unsigned Low,
                                         const SMTExprRef &Exp) {
  unsigned Width = High - Low + 1;
  return makeSMTLIBExpr(SMTExprKind::BVExtract, mkBVSort(Width),
                        "(_ extract " + utoa(High) + " " + utoa(Low) + ")",
                        {Exp});
}

SMTExprRef SMTLIBSolver::mkBVConcatImpl(const SMTExprRef &LHS,
                                        const SMTExprRef &RHS) {
  unsigned Width = LHS->getWidth() + RHS->getWidth();
  return makeSMTLIBExpr(SMTExprKind::BVConcat, mkBVSort(Width), "concat",
                        {LHS, RHS});
}

SMTExprRef SMTLIBSolver::mkArraySelectImpl(const SMTExprRef &Array,
                                           const SMTExprRef &Index) {
  return makeSMTLIBExpr(SMTExprKind::ArraySelect, Array->Sort->getElementSort(),
                        "select", {Array, Index});
}

SMTExprRef SMTLIBSolver::mkArrayStoreImpl(const SMTExprRef &Array,
                                          const SMTExprRef &Index,
                                          const SMTExprRef &Element) {
  return makeSMTLIBExpr(SMTExprKind::ArrayStore, Array->Sort, "store",
                        {Array, Index, Element});
}

// --- constants and symbols ---

SMTExprRef SMTLIBSolver::mkBoolImpl(bool b) {
  return makeSMTLIBExpr(SMTExprKind::BoolConst, mkBoolSort(),
                        b ? "true" : "false");
}

SMTExprRef SMTLIBSolver::mkBVFromDecImpl(int64_t Int, const SMTSortRef &Sort) {
  // Emit as a binary literal so we get correct two's-complement
  // sign-extension for widths > 64. The (_ bv<value> <width>) decimal form
  // would require big-integer arithmetic to handle that range, which we do
  // not have here. toTwosComplementBin handles all widths >= 1.
  const unsigned Width = Sort->getWidth();
  fatalErrorIf(Width == 0, "SMTLIBSolver: BV literal width must be non-zero");
  return makeSMTLIBExpr(SMTExprKind::BVConst, Sort,
                        "#b" + toTwosComplementBin(Int, Width));
}

SMTExprRef SMTLIBSolver::mkBVFromBinImpl(const std::string &Int,
                                         const SMTSortRef &Sort) {
  return makeSMTLIBExpr(SMTExprKind::BVConst, Sort, "#b" + Int);
}

SMTExprRef SMTLIBSolver::mkSymbolImpl(const std::string &Name,
                                      const SMTSortRef &Sort) {
  // Eagerly emit the declaration.
  std::string Quoted = quoteSymbol(Name);
  if (Sort->isFunctionSort()) {
    // (declare-fun f (D1 D2 ...) Codomain)
    std::string Decl = "(declare-fun " + Quoted + " (";
    const auto &Domain = Sort->getDomainSorts();
    for (std::size_t I = 0; I < Domain.size(); ++I) {
      if (I)
        Decl += " ";
      Decl += textOf(Domain[I]);
    }
    Decl += ") ";
    Decl += textOf(Sort->getCodomainSort());
    Decl += ")";
    emitLine(Decl);
  } else {
    emitLine("(declare-fun " + Quoted + " () " + textOf(Sort) + ")");
  }
  return makeSMTLIBExpr(SMTExprKind::Symbol, Sort, std::move(Quoted));
}

SMTExprRef SMTLIBSolver::mkArrayConstImpl(const SMTSortRef &IndexSort,
                                          const SMTExprRef &InitValue) {
  SMTSortRef Arr = mkArraySort(IndexSort, InitValue->Sort);
  // Materialize through a fresh `(define-fun)` rather than inlining. Two
  // reasons:
  //   1. mathsat's SMT-LIB parser rejects `(as const ...)` inside
  //      `(get-value ...)`, so any later expression that inlines the
  //      const-array literal and is queried via `(get-value ...)` would
  //      hit that parser bug. Binding the literal
  //      to a name once up front means every downstream expression
  //      references the bare symbol.
  //   2. (define-fun ...) is permanent under :global-declarations true and
  //      survives push/pop unchanged. Earlier we used (declare-fun) +
  //      (assert (= sym ...)), but the assertion is scoped — a const-array
  //      created inside a push() and used after pop() would have its
  //      defining equality dropped, leaving the symbol unconstrained
  //      (Codex review #2024-04 [high]).
  const std::string Name = "__CAMADA_aconst" + std::to_string(NextArrConstId++);
  std::string Quoted = quoteSymbol(Name);
  std::string LiteralText =
      "((as const " + textOf(Arr) + ") " + renderSMTLIBExpr(InitValue) + ")";
  std::string Defn =
      "(define-fun " + Quoted + " () " + textOf(Arr) + " " + LiteralText + ")";
  emitLine(Defn);
  return makeSMTLIBExpr(SMTExprKind::ArrayConst, Arr, std::move(Quoted));
}

// --- native FP literals + RM ---

// Camada's mkFPFromBin convention: FP is the full IEEE-754 bit string
// (sign + exponent + trailing-significand-without-hidden-bit). For FP32 that's
// 32 bits with a 23-bit trailing significand. SMT-LIB's (fp #b<s> #b<e> #b<m>)
// takes the same three components — the hidden bit is implicit there too.
SMTExprRef SMTLIBSolver::mkFPFromBinImpl(const std::string &FP,
                                         unsigned EWidth) {
  fatalErrorIf(FP.size() <= 1 + EWidth,
               "SMTLIBSolver: FP literal too short for declared widths");
  // Camada's mkFPSort(eb, sb) takes the trailing significand width (no hidden
  // bit), matching the cvc5 backend convention. The FP string is exactly
  // `1 + EWidth + SigWidth` bits long, so SigWidth = FP.size() - 1 - EWidth.
  unsigned SigWidth = FP.size() - 1 - EWidth;
  SMTSortRef Sort = mkFPSort(EWidth, SigWidth, FPEncoding::Native);
  std::string Sign = FP.substr(0, 1);
  std::string Exp = FP.substr(1, EWidth);
  std::string Sig = FP.substr(1 + EWidth);
  std::string Text = "(fp #b" + Sign + " #b" + Exp + " #b" + Sig + ")";
  return makeSMTLIBExpr(SMTExprKind::FPConst, Sort, std::move(Text));
}

SMTExprRef SMTLIBSolver::mkRMImpl(const RM &R) {
  const char *Name = nullptr;
  switch (R) {
  case RM::ROUND_TO_EVEN:
    Name = "roundNearestTiesToEven";
    break;
  case RM::ROUND_TO_AWAY:
    Name = "roundNearestTiesToAway";
    break;
  case RM::ROUND_TO_PLUS_INF:
    Name = "roundTowardPositive";
    break;
  case RM::ROUND_TO_MINUS_INF:
    Name = "roundTowardNegative";
    break;
  case RM::ROUND_TO_ZERO:
    Name = "roundTowardZero";
    break;
  }
  fatalErrorIf(!Name, "SMTLIBSolver: unknown rounding mode");
  return makeSMTLIBExpr(SMTExprKind::RMConst, mkRMSort(FPEncoding::Native),
                        Name);
}

SMTExprRef SMTLIBSolver::mkNaNImpl(bool Sgn, unsigned ExpWidth,
                                   unsigned SigWidth) {
  // (_ NaN eb sb) — sb here includes the hidden bit. Camada's mkNaN passes
  // SigWidth already including the hidden bit.
  SMTSortRef Sort = mkFPSort(ExpWidth, SigWidth - 1, FPEncoding::Native);
  std::string Text = "(_ NaN " + utoa(ExpWidth) + " " + utoa(SigWidth) + ")";
  // SMT-LIB has no signed-NaN literal — there is exactly one canonical NaN.
  // Callers that pass Sgn=true get the same value; that matches the cvc5 /
  // bitwuzla behavior (their NaN literals also ignore the sign).
  (void)Sgn;
  return makeSMTLIBExpr(SMTExprKind::FPConst, Sort, std::move(Text));
}

SMTExprRef SMTLIBSolver::mkInfImpl(bool Sgn, unsigned ExpWidth,
                                   unsigned SigWidth) {
  SMTSortRef Sort = mkFPSort(ExpWidth, SigWidth - 1, FPEncoding::Native);
  std::string Text = std::string("(_ ") + (Sgn ? "-" : "+") + "oo " +
                     utoa(ExpWidth) + " " + utoa(SigWidth) + ")";
  return makeSMTLIBExpr(SMTExprKind::FPConst, Sort, std::move(Text));
}

// --- native FP arithmetic + predicates ---

CAMADA_SMTLIB_UNARY(mkFPAbsImpl, "fp.abs", FPAbs, Exp->Sort)

SMTExprRef SMTLIBSolver::mkFPNegImpl(const SMTExprRef &Exp,
                                     FPNegBehavior Behavior) {
  // SMT-LIB's fp.neg has PreserveNaNPayload semantics — sign bit flipped on
  // non-NaNs, NaN payload preserved. That maps directly.
  if (Behavior == FPNegBehavior::PreserveNaNPayload)
    return makeSMTLIBExpr(SMTExprKind::FPNeg, Exp->Sort, "fp.neg", {Exp});

  // FlipSignBit must flip the top bit unconditionally, NaN included. SMT-LIB
  // has no direct op for that, so round-trip through the IEEE BV view: pull
  // the bits out, flip bit [N-1], reinterpret. mkIEEEFPToBV materializes a
  // fresh BV symbol constrained to Exp's bit pattern; mkBVToIEEEFP reads them
  // back as an FP value.
  unsigned Width =
      Exp->Sort->getFPExponentWidth() + Exp->Sort->getFPSignificandWidth() + 1;
  SMTExprRef Bits = mkIEEEFPToBV(Exp);
  SMTExprRef Sign = mkBVExtract(Width - 1, Width - 1, Bits);
  SMTExprRef Rest = mkBVExtract(Width - 2, 0, Bits);
  SMTExprRef Flipped = mkBVConcat(mkBVNot(Sign), Rest);
  return rewrapExprImpl(*mkBVToIEEEFP(Flipped, Exp->Sort), Exp->Sort,
                        SMTExprKind::FPNeg);
}

CAMADA_SMTLIB_UNARY(mkFPIsInfiniteImpl, "fp.isInfinite", FPIsInfinite,
                    mkBoolSort())
CAMADA_SMTLIB_UNARY(mkFPIsNaNImpl, "fp.isNaN", FPIsNaN, mkBoolSort())
CAMADA_SMTLIB_UNARY(mkFPIsDenormalImpl, "fp.isSubnormal", FPIsDenormal,
                    mkBoolSort())
CAMADA_SMTLIB_UNARY(mkFPIsNormalImpl, "fp.isNormal", FPIsNormal, mkBoolSort())
CAMADA_SMTLIB_UNARY(mkFPIsZeroImpl, "fp.isZero", FPIsZero, mkBoolSort())

CAMADA_SMTLIB_RM_BINARY(mkFPMulImpl, "fp.mul", FPMul)
CAMADA_SMTLIB_RM_BINARY(mkFPDivImpl, "fp.div", FPDiv)
CAMADA_SMTLIB_RM_BINARY(mkFPAddImpl, "fp.add", FPAdd)
CAMADA_SMTLIB_RM_BINARY(mkFPSubImpl, "fp.sub", FPSub)

CAMADA_SMTLIB_BINARY(mkFPRemImpl, "fp.rem", FPRem, LHS->Sort)

SMTExprRef SMTLIBSolver::mkFPSqrtImpl(const SMTExprRef &Exp,
                                      const SMTExprRef &R) {
  return makeSMTLIBExpr(SMTExprKind::FPSqrt, Exp->Sort, "fp.sqrt", {R, Exp});
}

SMTExprRef SMTLIBSolver::mkFPFMAImpl(const SMTExprRef &X, const SMTExprRef &Y,
                                     const SMTExprRef &Z, const SMTExprRef &R) {
  return makeSMTLIBExpr(SMTExprKind::FPFMA, X->Sort, "fp.fma", {R, X, Y, Z});
}

CAMADA_SMTLIB_BINARY(mkFPLtImpl, "fp.lt", FPLt, mkBoolSort())
CAMADA_SMTLIB_BINARY(mkFPGtImpl, "fp.gt", FPGt, mkBoolSort())
CAMADA_SMTLIB_BINARY(mkFPLeImpl, "fp.leq", FPLe, mkBoolSort())
CAMADA_SMTLIB_BINARY(mkFPGeImpl, "fp.geq", FPGe, mkBoolSort())
CAMADA_SMTLIB_BINARY(mkFPEqualImpl, "fp.eq", FPEqual, mkBoolSort())

#undef CAMADA_SMTLIB_UNARY
#undef CAMADA_SMTLIB_BINARY
#undef CAMADA_SMTLIB_RM_BINARY

SMTExprRef SMTLIBSolver::mkFPtoFPImpl(const SMTExprRef &From,
                                      const SMTSortRef &To,
                                      const SMTExprRef &R) {
  std::string Head = "(_ to_fp " + utoa(To->getFPExponentWidth()) + " " +
                     utoa(To->getFPSignificandWidth() + 1) + ")";
  return makeSMTLIBExpr(SMTExprKind::FPtoFP, To, std::move(Head), {R, From});
}

SMTExprRef SMTLIBSolver::mkSBVtoFPImpl(const SMTExprRef &From,
                                       const SMTSortRef &To,
                                       const SMTExprRef &R) {
  // Same opcode as fp→fp; SMT-LIB disambiguates by argument sort.
  std::string Head = "(_ to_fp " + utoa(To->getFPExponentWidth()) + " " +
                     utoa(To->getFPSignificandWidth() + 1) + ")";
  return makeSMTLIBExpr(SMTExprKind::SBVtoFP, To, std::move(Head), {R, From});
}

SMTExprRef SMTLIBSolver::mkUBVtoFPImpl(const SMTExprRef &From,
                                       const SMTSortRef &To,
                                       const SMTExprRef &R) {
  std::string Head = "(_ to_fp_unsigned " + utoa(To->getFPExponentWidth()) +
                     " " + utoa(To->getFPSignificandWidth() + 1) + ")";
  return makeSMTLIBExpr(SMTExprKind::UBVtoFP, To, std::move(Head), {R, From});
}

SMTExprRef SMTLIBSolver::mkFPtoSBVImpl(const SMTExprRef &From,
                                       unsigned ToWidth) {
  const SMTExprRef &R = mkRM(RM::ROUND_TO_ZERO, FPEncoding::Native);
  return makeSMTLIBExpr(SMTExprKind::FPtoSBV, mkBVSort(ToWidth),
                        "(_ fp.to_sbv " + utoa(ToWidth) + ")", {R, From});
}

SMTExprRef SMTLIBSolver::mkFPtoUBVImpl(const SMTExprRef &From,
                                       unsigned ToWidth) {
  const SMTExprRef &R = mkRM(RM::ROUND_TO_ZERO, FPEncoding::Native);
  return makeSMTLIBExpr(SMTExprKind::FPtoUBV, mkBVSort(ToWidth),
                        "(_ fp.to_ubv " + utoa(ToWidth) + ")", {R, From});
}

SMTExprRef SMTLIBSolver::mkFPtoIntegralImpl(const SMTExprRef &From,
                                            const SMTExprRef &R) {
  return makeSMTLIBExpr(SMTExprKind::FPtoIntegral, From->Sort,
                        "fp.roundToIntegral", {R, From});
}

SMTExprRef SMTLIBSolver::mkBVToIEEEFPImpl(const SMTExprRef &Exp,
                                          const SMTSortRef &To) {
  // ((_ to_fp eb sb) bv) form (no rounding mode) reinterprets a same-width BV
  // as an IEEE FP.
  std::string Head = "(_ to_fp " + utoa(To->getFPExponentWidth()) + " " +
                     utoa(To->getFPSignificandWidth() + 1) + ")";
  return makeSMTLIBExpr(SMTExprKind::BVToIEEEFP, To, std::move(Head), {Exp});
}

SMTExprRef SMTLIBSolver::mkIEEEFPToBVImpl(const SMTExprRef &Exp) {
  // Same trick as the cvc5 backend: SMT-LIB has no direct fp→bv that
  // preserves the IEEE bit pattern, so introduce a fresh BV symbol and tie it
  // back via the inverse direction.
  const std::string Name = "__CAMADA_ieeebv" + std::to_string(NextIEEEBVId++);
  SMTSortRef BVSort = mkBVSort(Exp->Sort->getFPExponentWidth() +
                               Exp->Sort->getFPSignificandWidth() + 1);
  SMTExprRef NewSymbol = mkSymbolUnchecked(Name, BVSort);
  addConstraint(mkEqual(Exp, mkBVToIEEEFP(NewSymbol, Exp->Sort)));
  return NewSymbol;
}

// --- Int / Real literals + arithmetic ---

// Integer literals in SMT-LIB are written as bare numerals, with `(- N)` for
// negatives — there is no signed numeric token.
SMTExprRef SMTLIBSolver::mkIntImpl(int64_t v) {
  std::string Text;
  if (v < 0) {
    // Avoid overflow when negating INT64_MIN. Build the magnitude as an
    // unsigned and stringify, then wrap in (- ...).
    uint64_t Mag = static_cast<uint64_t>(-(v + 1)) + 1;
    Text = "(- " + std::to_string(Mag) + ")";
  } else {
    Text = std::to_string(v);
  }
  return makeSMTLIBExpr(SMTExprKind::IntConst, mkIntSort(), std::move(Text));
}

SMTExprRef SMTLIBSolver::mkIntImpl(const std::string &v) {
  // Caller passes a decimal string, possibly leading '-'. Wrap with (- ...)
  // for the negative case so the wire form is canonical SMT-LIB.
  if (!v.empty() && v[0] == '-')
    return makeSMTLIBExpr(SMTExprKind::IntConst, mkIntSort(),
                          "(- " + v.substr(1) + ")");
  return makeSMTLIBExpr(SMTExprKind::IntConst, mkIntSort(), v);
}

SMTExprRef SMTLIBSolver::mkRealImpl(const std::string &v) {
  // Real literals: the input may be a decimal ("3.14"), an integer ("7"), a
  // signed integer ("-7"), or a rational like "3/4". Normalize to the form
  // SMT-LIB accepts in expression position: bare decimals/integers, with
  // (- ...) for negatives and (/ p q) for rationals.
  if (v.empty())
    return makeSMTLIBExpr(SMTExprKind::RealConst, mkRealSort(), "0.0");
  std::string Body = v;
  bool Negative = false;
  if (Body[0] == '-') {
    Negative = true;
    Body = Body.substr(1);
  }
  std::string Text;
  std::size_t Slash = Body.find('/');
  if (Slash != std::string::npos)
    Text = "(/ " + Body.substr(0, Slash) + " " + Body.substr(Slash + 1) + ")";
  else
    Text = Body;
  if (Negative)
    Text = "(- " + Text + ")";
  return makeSMTLIBExpr(SMTExprKind::RealConst, mkRealSort(), std::move(Text));
}

SMTExprRef SMTLIBSolver::mkRealImpl(int64_t v) {
  // Reuse the int64-stringify path, but mark the result Real-sorted.
  std::string Text;
  if (v < 0) {
    uint64_t Mag = static_cast<uint64_t>(-(v + 1)) + 1;
    Text = "(- " + std::to_string(Mag) + ")";
  } else {
    Text = std::to_string(v);
  }
  return makeSMTLIBExpr(SMTExprKind::RealConst, mkRealSort(), std::move(Text));
}

SMTExprRef SMTLIBSolver::mkRealImpl(int64_t num, int64_t den) {
  std::string NumText;
  std::string DenText = std::to_string(den < 0 ? -den : den);
  bool Negative = (num < 0) ^ (den < 0);
  uint64_t NumMag = num < 0 ? static_cast<uint64_t>(-(num + 1)) + 1
                            : static_cast<uint64_t>(num);
  NumText = std::to_string(NumMag);
  std::string Text = "(/ " + NumText + " " + DenText + ")";
  if (Negative)
    Text = "(- " + Text + ")";
  return makeSMTLIBExpr(SMTExprKind::RealConst, mkRealSort(), std::move(Text));
}

SMTExprRef SMTLIBSolver::mkArithNegImpl(const SMTExprRef &Exp) {
  return makeSMTLIBExpr(SMTExprKind::ArithNeg, Exp->Sort, "-", {Exp});
}

SMTExprRef SMTLIBSolver::mkArithAddImpl(const SMTExprRef &LHS,
                                        const SMTExprRef &RHS) {
  return makeSMTLIBExpr(SMTExprKind::ArithAdd, LHS->Sort, "+", {LHS, RHS});
}

SMTExprRef SMTLIBSolver::mkArithSubImpl(const SMTExprRef &LHS,
                                        const SMTExprRef &RHS) {
  return makeSMTLIBExpr(SMTExprKind::ArithSub, LHS->Sort, "-", {LHS, RHS});
}

SMTExprRef SMTLIBSolver::mkArithMulImpl(const SMTExprRef &LHS,
                                        const SMTExprRef &RHS) {
  return makeSMTLIBExpr(SMTExprKind::ArithMul, LHS->Sort, "*", {LHS, RHS});
}

SMTExprRef SMTLIBSolver::mkArithDivImpl(const SMTExprRef &LHS,
                                        const SMTExprRef &RHS) {
  // SMT-LIB uses `div` for integer arithmetic and `/` for real arithmetic.
  // Camada dispatches on operand sort, so this method receives both kinds —
  // pick the right token based on the LHS sort.
  const char *Op = LHS->Sort->isIntSort() ? "div" : "/";
  return makeSMTLIBExpr(SMTExprKind::ArithDiv, LHS->Sort, Op, {LHS, RHS});
}

SMTExprRef SMTLIBSolver::mkArithModImpl(const SMTExprRef &LHS,
                                        const SMTExprRef &RHS) {
  return makeSMTLIBExpr(SMTExprKind::ArithMod, mkIntSort(), "mod", {LHS, RHS});
}

SMTExprRef SMTLIBSolver::mkArithLtImpl(const SMTExprRef &LHS,
                                       const SMTExprRef &RHS) {
  return makeSMTLIBExpr(SMTExprKind::ArithLt, mkBoolSort(), "<", {LHS, RHS});
}

SMTExprRef SMTLIBSolver::mkArithGtImpl(const SMTExprRef &LHS,
                                       const SMTExprRef &RHS) {
  return makeSMTLIBExpr(SMTExprKind::ArithGt, mkBoolSort(), ">", {LHS, RHS});
}

SMTExprRef SMTLIBSolver::mkArithLeImpl(const SMTExprRef &LHS,
                                       const SMTExprRef &RHS) {
  return makeSMTLIBExpr(SMTExprKind::ArithLe, mkBoolSort(), "<=", {LHS, RHS});
}

SMTExprRef SMTLIBSolver::mkArithGeImpl(const SMTExprRef &LHS,
                                       const SMTExprRef &RHS) {
  return makeSMTLIBExpr(SMTExprKind::ArithGe, mkBoolSort(), ">=", {LHS, RHS});
}

SMTExprRef SMTLIBSolver::mkInt2RealImpl(const SMTExprRef &Exp) {
  return makeSMTLIBExpr(SMTExprKind::Int2Real, mkRealSort(), "to_real", {Exp});
}

SMTExprRef SMTLIBSolver::mkReal2IntImpl(const SMTExprRef &Exp) {
  return makeSMTLIBExpr(SMTExprKind::Real2Int, mkIntSort(), "to_int", {Exp});
}

SMTExprRef SMTLIBSolver::mkIsIntImpl(const SMTExprRef &Exp) {
  return makeSMTLIBExpr(SMTExprKind::IsInt, mkBoolSort(), "is_int", {Exp});
}

// --- UF + quantifiers ---

// (FuncName arg1 arg2 ...). The Function expression's text already carries
// the function symbol name (set when the symbol was declared).
SMTExprRef SMTLIBSolver::mkApplyImpl(const SMTExprRef &Function,
                                     const std::vector<SMTExprRef> &Args) {
  // Function is always a declared symbol, so its Head is the (quoted)
  // function name; the application node carries the operands.
  assert(toSolverExpr<SMTLIBExpr>(*Function).Expr.Args.empty() &&
         "Function expressions must be plain symbols");
  return makeSMTLIBExpr(SMTExprKind::Apply, Function->Sort->getCodomainSort(),
                        toSolverExpr<SMTLIBExpr>(*Function).Expr.Head, Args);
}

// Render a quantifier's bound-variable list `((v1 S1) (v2 S2) ...)`. Each var
// is a Symbol expression whose Head is the already-quoted variable name.
//
// Camada's regression tests pass quantifier vars that were created via
// mkSymbol — which means we already emitted `(declare-fun v () S)` at the
// global scope. The native backends silently accept this (Z3 ignores the
// redundant declaration; cvc5 shadows it inside the quantifier). The SMT-LIB
// pipeline mirrors that: the declaration was already emitted, we just
// reference the same name here in the binder list.
static std::string renderBinders(const std::vector<SMTExprRef> &Vars) {
  std::string Out;
  for (std::size_t I = 0; I < Vars.size(); ++I) {
    if (I)
      Out += " ";
    Out += "(";
    Out += static_cast<const SMTLIBExpr &>(*Vars[I]).Expr.Head;
    Out += " ";
    Out += static_cast<const SMTLIBSort &>(*Vars[I]->Sort).Sort;
    Out += ")";
  }
  return Out;
}

SMTExprRef SMTLIBSolver::mkForallImpl(const std::vector<SMTExprRef> &Vars,
                                      const SMTExprRef &Body) {
  return makeSMTLIBExpr(SMTExprKind::Forall, mkBoolSort(),
                        "forall (" + renderBinders(Vars) + ")", {Body},
                        /*OwnScope=*/true);
}

SMTExprRef SMTLIBSolver::mkExistsImpl(const std::vector<SMTExprRef> &Vars,
                                      const SMTExprRef &Body) {
  return makeSMTLIBExpr(SMTExprKind::Exists, mkBoolSort(),
                        "exists (" + renderBinders(Vars) + ")", {Body},
                        /*OwnScope=*/true);
}

// --- tuples ---

// Construct a tuple value: invoke the datatype constructor `<sortname>_mk`.
// SMT-LIB requires the bare constructor name (no parens) for 0-ary
// constructors and `(<ctor> e0 e1 ...)` otherwise.
SMTExprRef SMTLIBSolver::mkTupleImpl(const std::vector<SMTExprRef> &Elements) {
  std::vector<SMTSortRef> ElementSorts;
  ElementSorts.reserve(Elements.size());
  for (const auto &E : Elements)
    ElementSorts.push_back(E->Sort);
  SMTSortRef TupleSort = mkTupleSort(ElementSorts);
  const std::string &Name = static_cast<const SMTLIBSort &>(*TupleSort).Sort;
  if (Elements.empty())
    return makeSMTLIBExpr(SMTExprKind::TupleConst, TupleSort, Name + "_mk");
  return makeSMTLIBExpr(SMTExprKind::TupleConst, TupleSort, Name + "_mk",
                        Elements);
}

// Project tuple field i: (<sortname>_p<i> t).
SMTExprRef SMTLIBSolver::mkTupleSelectImpl(const SMTExprRef &Tuple,
                                           unsigned Index) {
  const std::string &Name = static_cast<const SMTLIBSort &>(*Tuple->Sort).Sort;
  SMTSortRef ElementSort = Tuple->Sort->getTupleElementSorts()[Index];
  return makeSMTLIBExpr(SMTExprKind::TupleSelect, ElementSort,
                        Name + "_p" + utoa(Index), {Tuple});
}

// --- write-only model queries / check ---

namespace {

// Given a `(get-value (<term>))` response of the form `((<term> <value>))`,
// extract `<value>`. Returns the value sub-expression with surrounding
// whitespace trimmed.
//
// The response is normalized by readOneSmtlibResponse so it's a single
// balanced sexpr. We strip the outer `(( ... ))` wrapping, then strip the
// `<term>` prefix (everything up to the first top-level whitespace), then
// trim.
std::string extractValueFromGetValue(const std::string &Resp) {
  // Standard SMT-LIB `(get-value (<term>))` returns
  //   ( (<term> <value>) )
  // but solvers vary on whitespace: some emit `((x #b...))`, mathsat emits
  // `( (|x| (_ bv5 8)) )` with spaces inside the outer parens, etc. Walk the
  // string lexically rather than pattern-matching exact bracket positions.
  auto skipWS = [](const std::string &S, std::size_t I) {
    while (I < S.size() &&
           (S[I] == ' ' || S[I] == '\t' || S[I] == '\n' || S[I] == '\r'))
      ++I;
    return I;
  };
  std::size_t I = skipWS(Resp, 0);
  if (I >= Resp.size() || Resp[I] != '(')
    return {};
  ++I; // consume outer '('
  I = skipWS(Resp, I);
  if (I >= Resp.size() || Resp[I] != '(')
    return {};
  ++I; // consume inner '(' opening the valuation pair
  // Skip the <term>: walk until top-level whitespace, respecting `|...|`,
  // `"..."`, and nested parens.
  int Depth = 0;
  bool InQuoted = false;
  bool InString = false;
  while (I < Resp.size()) {
    char C = Resp[I];
    if (InQuoted) {
      if (C == '|')
        InQuoted = false;
    } else if (InString) {
      if (C == '"')
        InString = false;
    } else if (C == '|') {
      InQuoted = true;
    } else if (C == '"') {
      InString = true;
    } else if (C == '(') {
      ++Depth;
    } else if (C == ')') {
      if (Depth == 0)
        return {}; // pair closed before a value appeared
      --Depth;
    } else if (Depth == 0 &&
               (C == ' ' || C == '\t' || C == '\n' || C == '\r')) {
      break;
    }
    ++I;
  }
  I = skipWS(Resp, I);
  // Find the closing `)` of the valuation pair, respecting nested structure.
  std::size_t Start = I;
  Depth = 0;
  InQuoted = false;
  InString = false;
  while (I < Resp.size()) {
    char C = Resp[I];
    if (InQuoted) {
      if (C == '|')
        InQuoted = false;
    } else if (InString) {
      if (C == '"')
        InString = false;
    } else if (C == '|') {
      InQuoted = true;
    } else if (C == '"') {
      InString = true;
    } else if (C == '(') {
      ++Depth;
    } else if (C == ')') {
      if (Depth == 0)
        break; // this is the inner `)` closing the pair
      --Depth;
    }
    ++I;
  }
  // Trim trailing whitespace from the value.
  std::size_t End = I;
  while (End > Start && (Resp[End - 1] == ' ' || Resp[End - 1] == '\t' ||
                         Resp[End - 1] == '\n' || Resp[End - 1] == '\r'))
    --End;
  return Resp.substr(Start, End - Start);
}

// Convert an SMT-LIB BV value literal into a binary string (no `#b` prefix).
// Handles `#b...`, `#x...`, and `(_ bv<n> <w>)` forms. Returns empty on
// failure.
std::string bvValueToBinary(const std::string &Value, unsigned Width) {
  if (Value.size() >= 2 && Value[0] == '#' && Value[1] == 'b')
    return Value.substr(2);
  if (Value.size() >= 2 && Value[0] == '#' && Value[1] == 'x') {
    // Hex: each digit -> 4 bits.
    std::string Bits;
    Bits.reserve((Value.size() - 2) * 4);
    for (std::size_t I = 2; I < Value.size(); ++I) {
      char C = Value[I];
      int N = 0;
      if (C >= '0' && C <= '9')
        N = C - '0';
      else if (C >= 'a' && C <= 'f')
        N = 10 + (C - 'a');
      else if (C >= 'A' && C <= 'F')
        N = 10 + (C - 'A');
      else
        return {};
      for (int B = 3; B >= 0; --B)
        Bits.push_back(((N >> B) & 1) ? '1' : '0');
    }
    // Trim leading zeros to fit the expected width if needed.
    if (Bits.size() > Width)
      Bits = Bits.substr(Bits.size() - Width);
    while (Bits.size() < Width)
      Bits.insert(Bits.begin(), '0');
    return Bits;
  }
  // (_ bv<n> <w>): parse the decimal value and convert.
  if (Value.size() >= 5 && Value.substr(0, 5) == "(_ bv") {
    std::size_t Start = 5;
    std::size_t End = Value.find(' ', Start);
    if (End == std::string::npos)
      return {};
    std::string Decimal = Value.substr(Start, End - Start);
    if (Decimal.empty())
      return {};
    for (char C : Decimal)
      if (C < '0' || C > '9')
        return {};
    // Repeated long-division by 2 over the decimal string, reading the
    // remainders out from least to most significant. This works at any width
    // without pulling in big-integer libraries.
    std::vector<unsigned char> Digits(Decimal.size());
    for (std::size_t I = 0; I < Decimal.size(); ++I)
      Digits[I] = Decimal[I] - '0';
    std::string Bits;
    Bits.reserve(Width);
    while (true) {
      bool NonZero = false;
      unsigned Carry = 0;
      for (unsigned char &D : Digits) {
        unsigned Cur = Carry * 10 + D;
        D = Cur / 2;
        Carry = Cur % 2;
        if (D != 0)
          NonZero = true;
      }
      Bits.push_back(Carry ? '1' : '0');
      if (!NonZero)
        break;
    }
    if (Bits.size() > Width)
      Bits.resize(Width); // truncate high bits beyond declared width
    while (Bits.size() < Width)
      Bits.push_back('0');
    std::reverse(Bits.begin(), Bits.end());
    return Bits;
  }
  return {};
}

// Skip ASCII whitespace.
std::size_t skipWhitespace(const std::string &S, std::size_t I) {
  while (I < S.size() &&
         (S[I] == ' ' || S[I] == '\t' || S[I] == '\n' || S[I] == '\r'))
    ++I;
  return I;
}

// Parse a `#b<bits>` or `#x<hex>` token starting at `I`, append `Width` bits
// to `Out` (left-padded with zeros if the literal is shorter, truncated if
// longer). Returns the index just past the token, or std::string::npos on
// failure. Z3 emits some FP components as `#x80` instead of `#b10000000`, so
// the parser must handle both forms.
std::size_t parseBVLiteralAppend(const std::string &S, std::size_t I,
                                 unsigned Width, std::string &Out) {
  if (I + 1 >= S.size() || S[I] != '#')
    return std::string::npos;
  std::string Bits;
  if (S[I + 1] == 'b') {
    I += 2;
    while (I < S.size() && (S[I] == '0' || S[I] == '1'))
      Bits.push_back(S[I++]);
  } else if (S[I + 1] == 'x') {
    I += 2;
    while (I < S.size()) {
      char C = S[I];
      int N = 0;
      if (C >= '0' && C <= '9')
        N = C - '0';
      else if (C >= 'a' && C <= 'f')
        N = 10 + (C - 'a');
      else if (C >= 'A' && C <= 'F')
        N = 10 + (C - 'A');
      else
        break;
      for (int B = 3; B >= 0; --B)
        Bits.push_back(((N >> B) & 1) ? '1' : '0');
      ++I;
    }
  } else {
    return std::string::npos;
  }
  if (Bits.size() > Width)
    Bits = Bits.substr(Bits.size() - Width);
  while (Bits.size() < Width)
    Bits.insert(Bits.begin(), '0');
  Out += Bits;
  return I;
}

// Convert an SMT-LIB native FP value literal into an IEEE-754 binary string
// of width `ExpWidth + EncodedSigWidth + 1` (sign + exp + significand without
// hidden bit). Handles `(fp #b<s> #b<e> #b<m>)` and `(_ {+,-}oo {+,-}zero NaN
// eb sb)` forms. SigWidth here is the encoded width (already excludes the
// hidden bit). Returns empty on parse failure.
std::string fpValueToBinary(const std::string &Value, unsigned ExpWidth,
                            unsigned SigWidth) {
  // (fp #b<s> #b<e> #b<m>): concat the three operands. Z3 may emit any of the
  // three components in #x... hex form when its bit width is a multiple of 4
  // (e.g. an 8-bit exponent comes back as #x80, not #b10000000).
  if (Value.size() >= 4 && Value.substr(0, 4) == "(fp ") {
    std::size_t I = 4;
    std::string Out;
    I = skipWhitespace(Value, I);
    I = parseBVLiteralAppend(Value, I, 1, Out);
    if (I == std::string::npos)
      return {};
    I = skipWhitespace(Value, I);
    I = parseBVLiteralAppend(Value, I, ExpWidth, Out);
    if (I == std::string::npos)
      return {};
    I = skipWhitespace(Value, I);
    I = parseBVLiteralAppend(Value, I, SigWidth, Out);
    if (I == std::string::npos)
      return {};
    if (Out.size() != 1 + ExpWidth + SigWidth)
      return {};
    return Out;
  }
  // (_ +oo eb sb), (_ -oo eb sb), (_ +zero eb sb), (_ -zero eb sb),
  // (_ NaN eb sb). Total width = 1 + eb + (sb - 1) since sb in this notation
  // includes the hidden bit.
  if (Value.size() >= 3 && Value.substr(0, 3) == "(_ ") {
    std::size_t I = skipWhitespace(Value, 3);
    std::size_t WordStart = I;
    while (I < Value.size() && Value[I] != ' ' && Value[I] != ')')
      ++I;
    std::string Tag = Value.substr(WordStart, I - WordStart);
    bool Sign = false;
    bool IsZero = false;
    bool IsInf = false;
    bool IsNaN = false;
    if (Tag == "+oo") {
      Sign = false;
      IsInf = true;
    } else if (Tag == "-oo") {
      Sign = true;
      IsInf = true;
    } else if (Tag == "+zero") {
      Sign = false;
      IsZero = true;
    } else if (Tag == "-zero") {
      Sign = true;
      IsZero = true;
    } else if (Tag == "NaN") {
      IsNaN = true;
    } else {
      return {};
    }
    std::string Bits;
    Bits.push_back(Sign ? '1' : '0');
    if (IsZero) {
      Bits.append(ExpWidth, '0');
      Bits.append(SigWidth, '0');
    } else if (IsInf) {
      Bits.append(ExpWidth, '1');
      Bits.append(SigWidth, '0');
    } else if (IsNaN) {
      Bits.append(ExpWidth, '1');
      // Canonical NaN: top significand bit set, rest zero. (Camada's signed
      // NaN convention reads the sign bit as 0.)
      Bits.push_back('1');
      if (SigWidth >= 1)
        Bits.append(SigWidth - 1, '0');
    }
    return Bits;
  }
  return {};
}

// Trim ASCII whitespace from both ends of S.
std::string trimWS(const std::string &S) {
  std::size_t I = 0;
  std::size_t J = S.size();
  while (I < J && (S[I] == ' ' || S[I] == '\t' || S[I] == '\n' || S[I] == '\r'))
    ++I;
  while (J > I && (S[J - 1] == ' ' || S[J - 1] == '\t' || S[J - 1] == '\n' ||
                   S[J - 1] == '\r'))
    --J;
  return S.substr(I, J - I);
}

// Strip a `<number>.0...` decimal tail if the fractional part is all zeros,
// otherwise leave the string alone. This lets us treat z3's (/ 3.0 4.0) and
// cvc5's (/ 3 4) uniformly.
std::string normalizeNumeric(const std::string &S) {
  std::size_t Dot = S.find('.');
  if (Dot == std::string::npos)
    return S;
  for (std::size_t I = Dot + 1; I < S.size(); ++I)
    if (S[I] != '0')
      return S; // non-zero fractional digit; keep the original
  return S.substr(0, Dot);
}

// Convert a possibly-decimal numeric string into an integer / fraction pair.
// "3" → ("3", "1"), "3.0" → ("3", "1"), "0.5" → ("5", "10"),
// "1.25" → ("125", "100"). Returns false on any character outside [0-9.].
bool decimalToFraction(const std::string &S, std::string &Num,
                       std::string &Den) {
  if (S.empty())
    return false;
  std::size_t Dot = S.find('.');
  if (Dot == std::string::npos) {
    for (char C : S)
      if (C < '0' || C > '9')
        return false;
    Num = S;
    Den = "1";
    return true;
  }
  std::string Whole = S.substr(0, Dot);
  std::string Frac = S.substr(Dot + 1);
  for (char C : Whole)
    if (C < '0' || C > '9')
      return false;
  for (char C : Frac)
    if (C < '0' || C > '9')
      return false;
  Num = Whole + Frac;
  // Strip leading zeros from numerator (but keep "0").
  std::size_t Start = Num.find_first_not_of('0');
  if (Start == std::string::npos)
    Num = "0";
  else
    Num = Num.substr(Start);
  Den = "1" + std::string(Frac.size(), '0');
  return true;
}

// Parse an SMT-LIB integer model value into a signed decimal string.
// Accepted shapes: `N`, `(- N)` where N is a non-negative integer literal.
// Returns the empty string on failure.
// Forward declaration; full definition follows. intValueToDecimal reuses the
// rational parser so it accepts the same wire shapes (decimals, rationals,
// signed forms) and only returns success if the value is integral.
bool rationalValueToFraction(const std::string &Value, std::string &Num,
                             std::string &Den);

// Decimal long division: divide non-negative decimal string Num by
// non-negative decimal string Den. If the division is exact, set Quotient
// to the result and return true; otherwise return false. Both inputs must
// be non-empty and contain only digits, with no leading sign.
bool decimalDivideExact(const std::string &Num, const std::string &Den,
                        std::string &Quotient) {
  if (Den.empty() || (Den.size() == 1 && Den[0] == '0'))
    return false;
  if (Num.empty())
    return false;

  // Standard schoolbook long division: walk Num left-to-right, build a
  // running remainder, and compute one quotient digit per Num digit.
  // Compare-and-subtract on decimal strings is enough; we don't need
  // arbitrary-precision arithmetic for typical SMT-LIB rational values.
  auto cmpDecimal = [](const std::string &A, const std::string &B) -> int {
    // Strip leading zeros for the comparison.
    std::size_t Ai = 0;
    while (Ai + 1 < A.size() && A[Ai] == '0')
      ++Ai;
    std::size_t Bi = 0;
    while (Bi + 1 < B.size() && B[Bi] == '0')
      ++Bi;
    std::size_t ALen = A.size() - Ai;
    std::size_t BLen = B.size() - Bi;
    if (ALen != BLen)
      return ALen < BLen ? -1 : 1;
    return A.compare(Ai, ALen, B, Bi, BLen) < 0   ? -1
           : A.compare(Ai, ALen, B, Bi, BLen) > 0 ? 1
                                                  : 0;
  };
  auto subDecimal = [](const std::string &A,
                       const std::string &B) -> std::string {
    // Compute A - B assuming A >= B and both are non-negative decimals.
    std::string Out(A.size(), '0');
    int Borrow = 0;
    std::size_t Ai = A.size();
    std::size_t Bi = B.size();
    while (Ai > 0) {
      --Ai;
      int Digit = (A[Ai] - '0') - Borrow;
      if (Bi > 0) {
        --Bi;
        Digit -= (B[Bi] - '0');
      }
      if (Digit < 0) {
        Digit += 10;
        Borrow = 1;
      } else {
        Borrow = 0;
      }
      Out[Ai] = static_cast<char>('0' + Digit);
    }
    // Strip leading zeros.
    std::size_t Start = Out.find_first_not_of('0');
    if (Start == std::string::npos)
      return "0";
    return Out.substr(Start);
  };

  std::string Q;
  std::string R = "0";
  for (char C : Num) {
    if (C < '0' || C > '9')
      return false;
    // R = R * 10 + digit
    if (R == "0")
      R = std::string(1, C);
    else
      R.push_back(C);
    // Strip a leading zero introduced by appending to "0".
    if (R.size() > 1 && R[0] == '0')
      R.erase(0, 1);
    // Find largest digit d (0-9) such that d*Den <= R.
    int D = 0;
    std::string Multiple = "0";
    for (int Try = 1; Try <= 9; ++Try) {
      // Compute Try * Den incrementally.
      std::string Next;
      int Carry = 0;
      for (std::size_t I = Den.size(); I-- > 0;) {
        int Digit = (Den[I] - '0') * Try + Carry;
        Next.insert(Next.begin(), static_cast<char>('0' + Digit % 10));
        Carry = Digit / 10;
      }
      while (Carry > 0) {
        Next.insert(Next.begin(), static_cast<char>('0' + Carry % 10));
        Carry /= 10;
      }
      if (cmpDecimal(Next, R) > 0)
        break;
      D = Try;
      Multiple = Next;
    }
    Q.push_back(static_cast<char>('0' + D));
    R = subDecimal(R, Multiple);
  }
  if (R != "0")
    return false;
  // Strip leading zeros from quotient, leaving at least one digit.
  std::size_t Start = Q.find_first_not_of('0');
  if (Start == std::string::npos)
    Quotient = "0";
  else
    Quotient = Q.substr(Start);
  return true;
}

std::string intValueToDecimal(const std::string &Value) {
  // Camada's getInt() is sometimes called on Real expressions whose model
  // value happens to be integral (e.g. `getInt(r + 1/2)` where r = 3/2 →
  // value 2). Solvers report such values in several shapes:
  //   - "2"            (cvc5, yices, mathsat for integer-typed)
  //   - "2.0"          (z3 for Real-typed)
  //   - "(/ 4 2)"      (any solver that emits unreduced rationals — e.g.
  //                     mathsat's Real model values aren't always reduced)
  //   - "(- 5)"        (negative integer)
  //   - "(- (/ 4 2))"  (negative integer via unreduced rational)
  // Reuse the rational parser so every shape collapses to a (Num, Den)
  // pair, then succeed if the division is exact.
  std::string Num, Den;
  if (!rationalValueToFraction(Value, Num, Den))
    return {};
  if (Den == "1")
    return Num;

  // Den != "1": exact-divide Num by Den. Strip the sign first so the
  // divider only sees non-negative magnitudes.
  bool Negative = !Num.empty() && Num[0] == '-';
  std::string NumMag = Negative ? Num.substr(1) : Num;
  std::string Quotient;
  if (!decimalDivideExact(NumMag, Den, Quotient))
    return {};
  if (Negative && Quotient != "0")
    return "-" + Quotient;
  return Quotient;
}

// Parse an SMT-LIB rational/real model value into a (numerator, denominator)
// pair of decimal strings. Both can be negative; the convention is that the
// numerator carries the sign and the denominator is non-negative.
//
// Accepted shapes:
//   N                       (integer)
//   (- N)                   (negative integer)
//   D                       (decimal: "3.14")
//   (- D)                   (negative decimal)
//   (/ p q)                 (rational; p and q are integer or decimal)
//   (- (/ p q))             (negative rational)
//   (/ (- p) q), (/ p (- q))  (rare but valid)
bool rationalValueToFraction(const std::string &Value, std::string &Num,
                             std::string &Den) {
  std::string V = trimWS(Value);
  // Strip a leading (- ...) negation, recurse, and flip the numerator sign.
  if (V.size() >= 4 && V[0] == '(' && V[1] == '-' && V[2] == ' ' &&
      V.back() == ')') {
    std::string Inner = trimWS(V.substr(3, V.size() - 4));
    if (!rationalValueToFraction(Inner, Num, Den))
      return false;
    if (!Num.empty() && Num[0] == '-')
      Num = Num.substr(1);
    else
      Num = "-" + Num;
    return true;
  }
  // (/ p q): parse p and q recursively as numerics.
  if (V.size() >= 4 && V.substr(0, 3) == "(/ " && V.back() == ')') {
    // Walk the body to split p and q at top-level whitespace.
    std::string Body = V.substr(3, V.size() - 4);
    int Depth = 0;
    std::size_t Split = std::string::npos;
    for (std::size_t I = 0; I < Body.size(); ++I) {
      if (Body[I] == '(')
        ++Depth;
      else if (Body[I] == ')')
        --Depth;
      else if (Depth == 0 &&
               (Body[I] == ' ' || Body[I] == '\t' || Body[I] == '\n')) {
        Split = I;
        break;
      }
    }
    if (Split == std::string::npos)
      return false;
    std::string P = trimWS(Body.substr(0, Split));
    std::string Q = trimWS(Body.substr(Split + 1));
    std::string PNum, PDen, QNum, QDen;
    if (!rationalValueToFraction(P, PNum, PDen))
      return false;
    if (!rationalValueToFraction(Q, QNum, QDen))
      return false;
    // (PNum/PDen) / (QNum/QDen) = (PNum*QDen) / (PDen*QNum). For the common
    // case where PDen and QDen are both "1" this collapses to PNum/QNum.
    if (PDen == "1" && QDen == "1") {
      Num = PNum;
      Den = QNum;
    } else {
      // Cross-multiplication on decimal strings would need a multi-precision
      // helper; we don't expect solvers to nest decimals inside (/ ...) in
      // practice, so flag the unhandled shape rather than approximating.
      return false;
    }
    // Move sign to numerator if it ended up on Den.
    if (!Den.empty() && Den[0] == '-') {
      Den = Den.substr(1);
      if (!Num.empty() && Num[0] == '-')
        Num = Num.substr(1);
      else
        Num = "-" + Num;
    }
    return true;
  }
  // Bare numeric (possibly decimal).
  std::string Norm = normalizeNumeric(V);
  return decimalToFraction(Norm, Num, Den);
}

} // namespace

std::string SMTLIBSolver::parseIntModelValueForTest(const std::string &Value) {
  return intValueToDecimal(Value);
}

SMTResult<std::string> SMTLIBSolver::sendGetValue(const SMTExprRef &Exp,
                                                  std::string &Resp) {
  if (!Proc)
    return SMTError{SMTErrorCode::UnsupportedOperation, SMTBackendKind::SMTLIB,
                    "SMTLIBSolver write-only mode does not support get*"};

  const std::string Cmd = "(get-value (" + renderSMTLIBExpr(Exp) + "))\n";
  if (File)
    File->emitRaw(Cmd);
  Proc->emitRaw(Cmd);
  Proc->flush();
  Resp = Proc->readResponse();
  return extractValueFromGetValue(Resp);
}

SMTResult<bool> SMTLIBSolver::getBoolImpl(const SMTExprRef &Exp) {
  std::string Resp;
  SMTResult<std::string> Value = sendGetValue(Exp, Resp);
  if (!Value)
    return Value.error();
  if (Value.value() == "true")
    return true;
  if (Value.value() == "false")
    return false;
  return SMTError{SMTErrorCode::BackendError, SMTBackendKind::SMTLIB,
                  "SMTLIBSolver: unexpected get-value response: " + Resp};
}

SMTResult<std::string> SMTLIBSolver::getBVInBinImpl(const SMTExprRef &Exp) {
  std::string Resp;
  SMTResult<std::string> Value = sendGetValue(Exp, Resp);
  if (!Value)
    return Value.error();
  std::string Bits = bvValueToBinary(Value.value(), Exp->getWidth());
  if (Bits.empty())
    return SMTError{SMTErrorCode::BackendError, SMTBackendKind::SMTLIB,
                    "SMTLIBSolver: could not parse BV value: " + Resp};
  return Bits;
}

SMTResult<std::string> SMTLIBSolver::getFPInBinImpl(const SMTExprRef &Exp) {
  // For BV-encoded FP, the base-class default routes through getBVInBin and
  // works fine. This override is only reached for native FP sorts.
  std::string Resp;
  SMTResult<std::string> Value = sendGetValue(Exp, Resp);
  if (!Value)
    return Value.error();

  unsigned ExpWidth = Exp->Sort->getFPExponentWidth();
  unsigned SigWidth = Exp->Sort->getFPSignificandWidth(); // excludes hidden bit
  std::string Bits = fpValueToBinary(Value.value(), ExpWidth, SigWidth);
  if (Bits.empty())
    return SMTError{SMTErrorCode::BackendError, SMTBackendKind::SMTLIB,
                    "SMTLIBSolver: could not parse FP value: " + Resp};
  return Bits;
}

SMTResult<std::string> SMTLIBSolver::getIntImpl(const SMTExprRef &Exp) {
  std::string Resp;
  SMTResult<std::string> Value = sendGetValue(Exp, Resp);
  if (!Value)
    return Value.error();
  std::string Decimal = intValueToDecimal(Value.value());
  if (Decimal.empty())
    return SMTError{SMTErrorCode::BackendError, SMTBackendKind::SMTLIB,
                    "SMTLIBSolver: could not parse Int value: " + Resp};
  return Decimal;
}

SMTResult<std::pair<std::string, std::string>>
SMTLIBSolver::getRationalImpl(const SMTExprRef &Exp) {
  std::string Resp;
  SMTResult<std::string> Value = sendGetValue(Exp, Resp);
  if (!Value)
    return Value.error();
  std::string Num, Den;
  if (!rationalValueToFraction(Value.value(), Num, Den))
    return SMTError{SMTErrorCode::BackendError, SMTBackendKind::SMTLIB,
                    "SMTLIBSolver: could not parse Real value: " + Resp};
  return std::make_pair(Num, Den);
}

SMTExprRef SMTLIBSolver::getArrayElementImpl(const SMTExprRef &Array,
                                             const SMTExprRef &Index) {
  // The native backends evaluate (select Array Index) against their cached
  // model. Over the SMT-LIB pipe we don't have a cached model — but the
  // child solver does, so building a (select ...) expression and letting the
  // caller's subsequent get* call dispatch (get-value ((select ...))) gives
  // the same observable result.
  return mkArraySelect(Array, Index);
}

bool SMTLIBSolver::supportsImpl(SolverFeature Feature) const {
  switch (Feature) {
  // These bits describe what the emitter can put on the wire; a given
  // child solver may still reject a construct at runtime (yices-smt2 has
  // no FP, bitwuzla no Int/Real, ...).
  case SolverFeature::IntRealArithmetic:
  case SolverFeature::Quantifiers:
  case SolverFeature::UninterpretedFunctions:
  case SolverFeature::NativeFloatingPoint:
    return true;
  // Unlike the wire-capability bits above, this one IS known: the
  // preamble already learned whether the child accepted
  // :produce-unsat-assumptions (false in write-only mode, where there is
  // no model to query either).
  case SolverFeature::UnsatAssumptions:
    return UnsatAssumptionsSupported;
  case SolverFeature::Timeouts:
  case SolverFeature::ArrayModels:
    return false;
  case SolverFeature::NativeTuples:
  case SolverFeature::NativeConstantArrays:
    break; // answered by the common layer's hooks
  }
  return false;
}

checkResult SMTLIBSolver::emitCheckCommand(const std::string &Cmd) {
  // Check commands are queries — they do NOT produce a `success` ack even
  // when :print-success is true. Bypass emitLine's resync logic; write the
  // command directly and read the sat/unsat/unknown line ourselves. In
  // write-only mode there is no response to read.
  if (File)
    File->emitRaw(Cmd);
  if (Proc) {
    Proc->emitRaw(Cmd);
    Proc->flush();
    const std::string Resp = Proc->readResponse();
    return Resp == "sat"     ? checkResult::SAT
           : Resp == "unsat" ? checkResult::UNSAT
                             : checkResult::UNKNOWN;
  }
  if (File)
    File->flush();
  return checkResult::UNKNOWN;
}

checkResult SMTLIBSolver::checkImpl() {
  return emitCheckCommand("(check-sat)\n");
}

checkResult
SMTLIBSolver::checkSatAssumingImpl(const std::vector<SMTExprRef> &Assumptions) {
  // Activate each assumption through a fresh literal: assert
  // (=> lit assumption), then assume the literal. This is equisatisfiable
  // with assuming the term directly, stays inside the standard's
  // literals-only grammar for (check-sat-assuming ...), and makes the
  // (get-unsat-assumptions) response trivially decodable by symbol name.
  // The implications remain asserted at the current push level after the
  // call; with the literals otherwise unconstrained they are vacuously
  // satisfiable, so later checks are unaffected.
  LastAssumptionLits.clear();
  std::string Cmd = "(check-sat-assuming (";
  for (const SMTExprRef &Assumption : Assumptions) {
    std::string Lit = "__CAMADA_assume_" + std::to_string(NextAssumeId++);
    addConstraint(mkImplies(mkSymbolUnchecked(Lit, mkBoolSort()), Assumption));
    if (!LastAssumptionLits.empty())
      Cmd.push_back(' ');
    Cmd.append(Lit);
    LastAssumptionLits.emplace_back(std::move(Lit), Assumption);
  }
  Cmd.append("))\n");
  return emitCheckCommand(Cmd);
}

SMTResult<std::vector<SMTExprRef>> SMTLIBSolver::getUnsatAssumptionsImpl() {
  if (!Proc)
    return SMTError{SMTErrorCode::BackendError, SMTBackendKind::SMTLIB,
                    "SMTLIBSolver: no child process to query for unsat "
                    "assumptions in write-only mode"};
  if (!UnsatAssumptionsSupported)
    return SMTError{SMTErrorCode::UnsupportedOperation, SMTBackendKind::SMTLIB,
                    "The child solver does not support "
                    ":produce-unsat-assumptions"};

  const std::string Cmd = "(get-unsat-assumptions)\n";
  if (File)
    File->emitRaw(Cmd);
  Proc->emitRaw(Cmd);
  Proc->flush();
  std::string Resp = Proc->readResponse();
  if (Resp.compare(0, 6, "(error") == 0 || Resp.empty())
    return SMTError{SMTErrorCode::BackendError, SMTBackendKind::SMTLIB,
                    "SMTLIBSolver: (get-unsat-assumptions) failed: " + Resp};

  // The response is a list of the assumed activation literals, e.g.
  // `(__CAMADA_assume_0 __CAMADA_assume_2)`. Tokenize and map each literal
  // back to the assumption it activated. `|` is a delimiter too: quoting
  // is semantically transparent in SMT-LIB, so a child may legally echo
  // the literals as `|__CAMADA_assume_0|`, and the names contain no `|`.
  std::vector<SMTExprRef> Result;
  std::string Token;
  auto FlushToken = [&]() {
    if (Token.empty())
      return;
    for (const auto &[Lit, Assumption] : LastAssumptionLits)
      if (Token == Lit) {
        Result.push_back(Assumption);
        break;
      }
    Token.clear();
  };
  for (const char C : Resp) {
    if (C == '(' || C == ')' || C == '|' || C == ' ' || C == '\t' ||
        C == '\n' || C == '\r') {
      FlushToken();
      continue;
    }
    Token.push_back(C);
  }
  FlushToken();
  return Result;
}

void SMTLIBSolver::resetImpl() {
  // (reset) is non-uniform across solvers:
  //   - z3, bitwuzla, yices: ack `(reset)` with `success`.
  //   - cvc5: no ack for `(reset)` (and resets :print-success in the process).
  //   - mathsat: acks `(reset)`, AND additionally acks each `(echo ...)` with
  //     a trailing `success` on top of the echoed content. Some solvers also
  //     reject `(get-info)` (bitwuzla), so the marker can't rely on that
  //     command being recognised.
  //
  // Strategy: send `(reset) (set-option :print-success true) (echo "...")`
  // — `(echo)` is the one resync command every supported child accepts.
  // Read until we see the marker (drains the leading success acks). Then
  // do a non-blocking drain to absorb any solver-specific extra acks
  // (mathsat's echo-ack, e.g.) so the protocol is back in lockstep before
  // emitPreamble() runs.
  if (File)
    File->emitRaw("(reset)\n");
  if (Proc) {
    Proc->emitRaw("(reset)\n");
    Proc->emitRaw("(set-option :print-success true)\n");
    Proc->emitRaw("(echo \"__camada_reset_marker__\")\n");
    Proc->flush();
    while (true) {
      std::string Resp = Proc->readResponse();
      fatalErrorIf(Resp.empty(),
                   "SMTLIBSolver: child solver closed the pipe during (reset)");
      if (Resp.find("__camada_reset_marker__") != std::string::npos)
        break;
    }
    // Drain any remaining stray responses (e.g. mathsat's echo-ack `success`
    // that arrives after the echoed content). 200ms is generous — the data
    // is already in the kernel pipe by the time we reach this point.
    Proc->drainResponses(200);
  }
  LastAssumptionLits.clear();
  emitPreamble();
}

void SMTLIBSolver::pushImpl(unsigned nscopes) {
  emitLine("(push " + std::to_string(nscopes) + ")");
}

void SMTLIBSolver::popImpl(unsigned nscopes) {
  emitLine("(pop " + std::to_string(nscopes) + ")");
}

void SMTLIBSolver::dumpImpl(std::string &Out) {
  Out = "SMTLIBSolver: dump-impl emits assertions to the configured stream.\n";
}

void SMTLIBSolver::dumpModelImpl(std::string &Out) {
  Out = "SMTLIBSolver write-only mode does not produce a model.\n";
}

std::string SMTLIBSolver::getSolverNameAndVersion() const {
  return "SMTLIB write-only";
}

} // namespace camada
