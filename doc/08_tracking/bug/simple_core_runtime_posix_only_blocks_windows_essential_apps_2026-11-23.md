# simple-core runtime is POSIX-only; essential apps cannot link it on x86_64-pc-windows-msvc (2026-11-23)

Status: OPEN (runtime and platform owner). Blocks every essential app built with
`--runtime-bundle simple-core` on Windows MSVC.

## Symptom

New Phase 1 seed (release `6816f70c47e`). The simple-core archive is complete and indexed:
- path: `build/essential-apps/simple-core/libsimple_runtime.a`
- sha256: `f0e8437cc87633507a6ffb62088d2f360accc714b0991b7923ad75bf8cf2104f`
- required symbols: all 86 `CORE_REQUIRED_RUNTIME_SYMBOLS` defined and in the archive index.

Built with the essential-apps script's flags (`--entry-closure --runtime-bundle simple-core
--strip --source src/compiler --source src/app --source src/lib`,
`SIMPLE_SIMPLE_CORE_PATH=<archive>`), `src/app/llm_caret/cs_main.spl` compiles in about 20 min,
then fails to link:

```
Build failed: link failed: 968 undefined symbol(s) with SIMPLE_NO_STUB_FALLBACK=1: __errno_location,
clock_gettime, closedir, fchmod, fcntl, fexecve, fork, fsync, getppid, gettimeofday, kill, ...
lld-link: error: undefined symbol: fork
>>> referenced by libsimple_runtime.a(mod_0.o):(.weak._sffi_core_process_fork.default._rt_debug_mode_enabled)
```

## Classification of the 968

1. **POSIX libc referenced by the simple-core runtime itself** (71 references from
   `libsimple_runtime.a`): `clock_gettime closedir fchmod fcntl fexecve fork fsync getppid
   gettimeofday kill link memfd_create mkdtemp mmap munmap opendir pipe2 readdir realpath setenv
   setpgid sigismember sigpending sysconf uname unsetenv usleep wait4 waitpid __errno_location`.
   `src/runtime/simple_core/*.spl` (for example `core_process`, `core_fs`) has no Windows
   implementation of these.
2. **`rt_*` outside the simple-core ABI that the app closures need**, by family: vulkan 91,
   process 91, simd 66, io 58, metal 41, cuda 39, windows 35, file 32, linux 29, rocm 28,
   oneapi 24, intel 21, opencl 20, math 20, and more.

## Consequence

Every simple-core row of the essential-apps check is BLOCKED on Windows MSVC for both
compilers: cs, messaging, dash, smux, orchestrator, ide, docker_runner, Caret, DevHub.
`scripts/check/check-bootstrap-essential-apps.shs` requires simple-core for DevHub and Caret,
so its Windows run cannot pass until this is resolved. The `core-c-bootstrap` lane is not a
substitute either (coordinator decision): Caret on it lacks 274 GPU/TLS `rt_*`.

## Unblock condition (owner decision)

Either give simple-core Windows implementations (Win32 equivalents for process, fs, time,
env and signal), together with provider lanes for the GPU/SIMD families, or define which
runtime bundle the essential apps use on Windows.
