# Domain research: filesystem-launched guest toolchains

Date: 2026-07-11

LLVM's cross-compilation guidance separates the machine running Clang from the
target for generated code and requires an explicit target triple and target
sysroot. LLVM's compiler cross-build guidance separately configures the host
triple of the produced compiler, which is the distinction this lane must prove:
host cross-Clang output is not evidence that Clang itself runs in SimpleOS.

- Clang cross-compilation: <https://clang.llvm.org/docs/CrossCompilation.html>
- Cross-building LLVM/Clang: <https://llvm.org/docs/HowToCrossCompileLLVM.html>
- POSIX executable-file model: <https://pubs.opengroup.org/onlinepubs/9799919799/functions/exec.html>

## Applied conclusions

- Treat `/usr/bin/clang` and its generated `hello.elf` as two separately proven
  executables.
- Load ELF program headers and `PT_LOAD` ranges from the mounted file instead of
  requiring one contiguous whole-file buffer.
- Preserve argv/env, exit status, and filesystem provenance across launch.
- A service readiness string is not a protocol oracle: HTTP needs a response;
  DB needs create/write/read state observed through the socket.

