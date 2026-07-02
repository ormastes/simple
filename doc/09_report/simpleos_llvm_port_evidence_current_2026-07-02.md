# SimpleOS LLVM Port Evidence Current - 2026-07-02

## Scope

Focused LLVM-to-SimpleOS port evidence for the current hardening lane.

## Results

| Gate | Status | Evidence |
| --- | --- | --- |
| Cross-build plan CLI | PASS | `SIMPLE_LIB=src bin/simple run src/os/port/llvm/build.spl -- --cross --print-plan` -> 5 targets: x86_64, aarch64, armv7, riscv64gc, riscv32imac |
| Cross-build subset plan CLI | PASS | `SIMPLE_LIB=src bin/simple run src/os/port/llvm/build.spl -- --cross --targets x86_64-unknown-simpleos,armv7-unknown-simpleos --print-plan` -> 2 targets; `--target armv7-unknown-simpleos --print-plan` -> 1 target |
| Host tblgen tools | PASS | `sh src/os/port/llvm/build.shs host-tools` -> built `build/os/llvm/host-tools/bin/llvm-tblgen` and `clang-tblgen` |
| Cross-build status CLI | PASS | `SIMPLE_LIB=src bin/simple run src/os/port/llvm/build.spl -- --cross --status` -> host-tools BUILT, sysroot READY; cross targets and compiler-rt targets NOT BUILT |
| Sysroot libc++ header/runtime staging | PASS | `SIMPLEOS_TARGET_TRIPLE=x86_64-unknown-simpleos sh src/os/port/llvm/sysroot.shs` -> staged libc++ under `build/os/sysroot/include/c++/v1`, generated `__config_site`, installed `__assertion_handler`, built `libc++.a`, and staged `crt0.o`, `libsimpleos_c.a`, and `libm.a` |
| x86_64 cross LLVM configure | PASS | `SIMPLEOS_TARGET_TRIPLE=x86_64-unknown-simpleos SIMPLE_TARGET=x86_64-unknown-simpleos sh src/os/port/llvm/build.shs cross` -> CMake configure/generate complete; build enters LLVM object compilation |
| Focused x86_64 `bin/lld` cross executable link | PASS | `make -C src/os/libc && SIMPLEOS_TARGET_TRIPLE=x86_64-unknown-simpleos sh src/os/port/llvm/sysroot.shs && ninja -C build/os/llvm/cross-x86_64-unknown-simpleos bin/lld` -> final executable link completes; `build/os/llvm/cross-x86_64-unknown-simpleos/bin/lld` exists and is executable, 64 MB |
| Focused x86_64 `bin/clang` cross executable link | PASS | `make -C src/os/libc && SIMPLEOS_TARGET_TRIPLE=x86_64-unknown-simpleos sh src/os/port/llvm/sysroot.shs && ninja -C build/os/llvm/cross-x86_64-unknown-simpleos bin/clang` -> final executable link completes; `build/os/llvm/cross-x86_64-unknown-simpleos/bin/clang` symlinks to executable `clang-20`, 125 MB |
| Cross-build plan scaffolding | PASS | `SIMPLE_LIB=src bin/simple test test/02_integration/os/port/llvm/cross_build_plan_spec.spl --mode=interpreter --clean` -> 18 examples, 0 failures |
| Per-target compiler-rt/build staging scaffolding | PASS | `SIMPLE_LIB=src bin/simple test test/02_integration/os/port/llvm/per_target_build_spec.spl --mode=interpreter --clean` -> 51 examples, 0 failures |
| Focused x86_64 compiler-rt builtins configure | PASS | `SIMPLEOS_TARGET_TRIPLE=x86_64-unknown-simpleos sh src/os/port/llvm/build.shs compiler-rt` now gets past CMake configure after removing the contradictory `COMPILER_RT_DEFAULT_TARGET_TRIPLE` flag and stale empty `CMAKE_*_FLAGS` cache values |
| Focused x86_64 compiler-rt builtins compile/stage | PASS | `make -C src/os/libc && SIMPLEOS_TARGET_TRIPLE=x86_64-unknown-simpleos sh src/os/port/llvm/sysroot.shs && SIMPLEOS_TARGET_TRIPLE=x86_64-unknown-simpleos sh src/os/port/llvm/build.shs compiler-rt` -> `builtins` builds 165/165 and stages `libclang_rt.builtins-x86_64.a` under `build/os/sysroot/lib/clang/19/lib/x86_64-unknown-simpleos/`; staged archive is 232 KB |
| Focused `Path.cpp` compile | PASS | direct clang++ compile with Ninja flags plus `-D__simpleos__=1` -> object builds; only existing futimes/futimens warning remains |
| Focused `AssignmentTrackingAnalysis.cpp` compile | PASS | direct clang++ compile with Ninja flags after replacing `std::stringstream` with `raw_string_ostream` -> object builds |
| Focused `MIRFSDiscriminator.cpp` compile | PASS | direct clang++ compile with Ninja flags after replacing `SampleProf.h` `std::ostringstream` use with `raw_string_ostream` -> object builds |
| Focused instrumentation hex compile | PASS | direct clang++ compile with Ninja flags for `InstrOrderFile.cpp` and `AddressSanitizer.cpp` after replacing iostream/iomanip hex formatting with `utohexstr` -> objects build |
| Focused `MemProfContextDisambiguation.cpp` compile | PASS | direct clang++ compile with Ninja flags after replacing iostream node id formatting with `Twine::utohexstr` -> object builds |
| Focused `ImportedFunctionsInliningStatistics.cpp` compile | PASS | direct clang++ compile with Ninja flags after replacing `stringstream` / `setprecision` with `raw_string_ostream` and LLVM `format("%.4g", ...)` -> object builds |
| Focused LLVM MC no-sstream compile | PASS | direct clang++ compile with Ninja flags for `MCPseudoProbe.cpp`, `MCParser/AsmParser.cpp`, and `MCParser/MasmParser.cpp` after replacing `std::ostringstream` with `raw_string_ostream` -> objects build |
| Focused coverage mapping no-sstream compile | PASS | direct clang++ compile with Ninja flags for `CoverageMappingWriter.cpp`, `CoverageMappingReader.cpp`, and `CoverageMapping.cpp` after replacing `CoverageMapping.h` `std::ostringstream` helpers with `raw_string_ostream` -> objects build |
| Focused `Host.cpp` target-parser compile | PASS | direct clang++ compile with Ninja flags after adding SimpleOS `sys/utsname.h` and `uname` libc stub -> object builds |
| Focused TextAPI `DylibReader.cpp` compile | PASS | direct clang++ compile with Ninja flags after replacing iostream UUID hex formatting with LLVM `format_hex_no_prefix` -> object builds |
| Focused LLD `ErrorHandler.cpp` compile | PASS | direct clang++ compile with Ninja flags after adding SimpleOS C/ASCII locale fallback declarations/stubs, `wctype.h`, and libc++ default rune table config -> object builds |
| Focused Clang Lex `PPMacroExpansion.cpp` compile | PASS | direct clang++ compile with Ninja flags after replacing `std::stringstream` / `std::locale` / `std::put_time` timestamp formatting with LLVM raw stream + `format` helper -> object builds |
| SimpleOS libc rebuild | PASS | `make -C src/os/libc` -> rebuilt `libsimpleos_c.a` including the C++ ABI, stdio, string, mman, and libm surfaces needed by the final LLD link |
| SimpleOS C++/POSIX surface probes | PASS | `clang++ --target=x86_64-unknown-simpleos --sysroot=build/os/sysroot ...` including `<string>`, `<mutex>`, `<shared_mutex>`, `<future>`, `<random>`, `gethostname`, `getsid`, `std::isxdigit`, `sys/resource.h`, `sys/socket.h`, `sys/un.h`, `sys/wait.h`, `pwd.h`, `alarm`, `setsid`, `getpagesize`, and signal flags compiles |
| Cross clang artifact-gated smoke | FAIL | Corrected smoke now probes canonical `bin/clang` with a 5s timeout and fails the first runtime gate: final direct `timeout 5s build/os/llvm/cross-x86_64-unknown-simpleos/bin/clang --print-target-triple` exits 124 and writes 0 bytes. Interrupt backtrace parks in `simpleos_syscall` via `stat()` -> `llvm::sys::fs::status` -> `clang::driver::Driver::loadDefaultConfigFiles()` |

## Current Frontier

The focused x86_64 LLD and Clang builds now complete through final executable
link. The missing-symbol class for libc++ headers, pthread condition variables,
`strerror_r`, wide numeric conversion functions, aligned/nothrow C++
allocation, thread-local destructors, `vfprintf`, `wmemcmp`, `strpbrk`, `erf`,
`logb`, `rint`, `mprotect`, libc++ regex/locale pulls, SimpleOS C++ entry shim,
and Clang driver `getrlimit`/`setrlimit` stack probing is cleared for this
target.

The canonical cross clang artifact is now present at
`build/os/llvm/cross-x86_64-unknown-simpleos/bin/clang` as a symlink to
`clang-20`, but host-running it currently times out before printing the target
triple or resource dir. This session cleared the earlier `_start` BSS crash
with `__bss_end=_end`, added Linux-host fallback paths for constructor
allocation/write/exit and `fstat`, and preserved host argc/argv/envp in crt0 so
LLVM reaches Clang driver config loading. The next concrete blocker is the
path-based `stat()` host-smoke fallback: `--print-target-triple` now hangs in
`simpleos_syscall` from `stat()` while `Driver::loadDefaultConfigFiles()` checks
default config paths.

Compiler-rt staging has advanced through x86_64 builtins compile and archive
staging. Broader target rollout and resource-dir integration remain gated on
finishing the host-smoke runtime shim far enough for canonical Clang to report
`x86_64-simpleos` and run the compile/link smoke.

## Spec Maintenance Completed

- Fixed `build.spl -- --cross --print-plan` / `--status` dispatch by stripping
  the runner separator before checking `--cross`.
- Added the missing `armv7-unknown-simpleos` -> LLVM `ARM` arch mapping used by
  the live plan command and shell build script.
- Fixed documented `--targets <csv>` handling so multi-target subset plans do
  not collapse into one invalid target.
- Removed the stale `process.run_with_env` call from staged cross-build shell
  delegation.
- Built host LLVM tblgen tools and added an explicit C++ standard-header
  preflight for cross-stage configure.
- Staged libc++ headers into `include/c++/v1`, generated the minimal libc++
  config/assertion handler, and added SimpleOS C header shims needed by LLVM
  (`ctype.h`, `inttypes.h`, `bits/types/mbstate_t.h`, `machine/endian.h`).
- Staged a minimal libc++ runtime archive into `build/os/sysroot/lib/libc++.a`
  and linked SimpleOS runtime archives after LLVM target archives via
  `CMAKE_CXX_STANDARD_LIBRARIES`.
- Added `-Wl,-no-pie` to the SimpleOS LLVM toolchain so the static SimpleOS
  startup/runtime objects are linked as a non-PIE executable.
- Marked the LLVM CMake toolchain as Unix-style for LLVM Support so generated
  config exposes POSIX file/path APIs such as `file_status::getSize` and
  `EnvPathSeparator`.
- Added the minimal `sysexits.h` surface required by LLVM's Unix exit-code
  branch (`EX_IOERR`).
- Enabled libc++ wide characters, pthread-backed thread declarations, monotonic
  clock, and random-device declarations in the staged `__config_site`.
- Added the SimpleOS libc declarations/stubs needed for the first LLVM Support
  object wave: wide-character search helpers, `sched_yield`, pthread rwlock
  declarations, recursive mutex attributes, `pthread_cond_timedwait`,
  `isxdigit`, `gethostname`, and `getsid`.
- Added the next POSIX process/signal/socket/userdb surfaces used by LLVM
  Support: `alarm`, `_exit`, `setsid`, `wait4`, `getrusage`, `strsignal`,
  signal action flags, `pwd.h`, `sys/socket.h`, `sys/un.h`, `sys/file.h`, and
  `sys/statvfs.h` with ENOSYS/no-op stubs where SimpleOS has no backing service.
- Added the next POSIX filesystem declarations/stubs used by LLVM `Path.cpp`:
  `symlink`, `link`, `readlink`, `fchmod`, `fchown`, `umask`, `madvise`,
  `struct flock`, `F_SETLK`, `F_SETLKW`, `S_ISSOCK`, and `MNT_LOCAL`.
- Recorded and applied LLVM patch notes for `raw_os_ostream` under
  no-localization libc++, SimpleOS `GetMainExecutable` argv0 fallback, and
  `AssignmentTrackingAnalysis.cpp` / `SampleProf.h` `raw_string_ostream` string
  formatting.
- Recorded and applied LLVM instrumentation patch notes for replacing
  iostream/iomanip hex formatting with LLVM `utohexstr` in `InstrOrderFile.cpp`
  and `AddressSanitizer.cpp`.
- Recorded and applied LLVM MemProf patch notes for replacing iostream node id
  formatting with `Twine::utohexstr` in `MemProfContextDisambiguation.cpp`.
- Recorded and applied LLVM imported-function stats patch notes for replacing
  `stringstream` / `setprecision` with `raw_string_ostream` plus LLVM
  `format("%.4g", ...)`.
- Recorded and applied LLVM MC patch notes for replacing `std::ostringstream`
  with `raw_string_ostream` in `MCPseudoProbe.cpp`, `MCParser/AsmParser.cpp`,
  and `MCParser/MasmParser.cpp`.
- Recorded and applied LLVM coverage mapping patch notes for replacing MCDC
  helper `std::ostringstream` uses with `raw_string_ostream`.
- Added the minimal SimpleOS `sys/utsname.h` header and `uname` libc stub used
  by LLVM `TargetParser/Unix/Host.inc`.
- Recorded and applied LLVM TextAPI DylibReader patch notes for replacing
  iostream UUID hex formatting with LLVM `format_hex_no_prefix`.
- Added the minimal SimpleOS C/ASCII locale declarations/stubs needed by
  libc++ regex and LLD `ErrorHandler.cpp`: `locale_t`, `LC_*_MASK`,
  `newlocale`/`freelocale`/`uselocale`, `*_l` numeric/string/time/ctype
  wrappers, multibyte/wide conversion helpers, `wctype.h`, and libc++ default
  rune table config.
- Recorded and applied Clang Lex patch notes for replacing `std::put_time` and
  `std::stringstream` `__TIMESTAMP__` formatting with LLVM raw streams plus
  fixed C-locale weekday/month names in `PPMacroExpansion.cpp`.
- Added the final focused LLD link libc/ABI surface: aligned and nothrow C++
  allocation/delete wrappers, `__cxa_thread_atexit`, weak C `main` forwarding
  for SimpleOS C++ entry points, `vfprintf`, `mprotect`, `wmemcmp`, `logb`,
  `erf`, and `rint`.
- Recorded and applied the LLD `ErrorHandler.cpp` no-regex patch for SimpleOS,
  keeping normal diagnostics while avoiding libc++ locale/regex runtime pulls
  under `_LIBCPP_HAS_LOCALIZATION=0`.
- Recorded and applied the consolidated Clang no-iostream/fstream target patch:
  CrossTU, Analysis, ThreadSafety, UnsafeBufferUsage, BareMetal driver, and
  Frontend file reads now use LLVM `raw_string_ostream` / `raw_ostream` /
  `MemoryBuffer` instead of target-side iostream/fstream/stringstream.
- Added the SimpleOS `sys/resource.h` `rlimit` surface and libc
  `getrlimit`/`setrlimit` stack-resource stubs required by Clang `cc1_main`.
- Added `strpbrk` to SimpleOS libc and C++ `<cstring>` so Clang builtin format
  classification links against the SimpleOS runtime.
- Added `__simpleos__` as an explicit toolchain macro because Clang does not
  currently predefine one for `*-unknown-simpleos` triples.
- Pinned `HAVE_GETPAGESIZE`, `HAVE_SYSCONF`, and `HAVE_GETRUSAGE` in the
  SimpleOS LLVM toolchain because the freestanding CMake symbol checks miss
  sysroot-provided libc symbols.
- Updated stale `fs.read_to_text` usage to current process-backed file reads for
  the static specs.
- Updated stale direct bool matcher calls to `expect(...).to_equal(true)` via a
  local `check` helper.
- Updated the static target assertions to include the current
  `armv7-unknown-simpleos` target.
- Updated process result checks to the current `ProcessResult` fields.
- Removed the host-clang fallback from `smoke_clang_spec.spl`; live assertions
  now run only against the canonical SimpleOS cross-build artifact path.
- Guarded smoke execution so absent or non-host-runnable cross artifacts do not
  create false failures, while host-runnable canonical artifacts still compile
  and link the `hello.c` smoke.
- Fixed compiler-rt stage configure by removing the incompatible
  `COMPILER_RT_DEFAULT_TARGET_TRIPLE` override when
  `COMPILER_RT_DEFAULT_TARGET_ONLY=ON`.
- Removed preload-time `CMAKE_*_FLAGS` sysroot injection from
  `compiler_rt_cmake.cmake`; the SimpleOS toolchain owns sysroot/freestanding
  flags, and the wrapper now unsets stale cached flag values.
- Narrowed compiler-rt stage 3 to `ninja ... builtins` and staged only
  `libclang_rt.builtins*.a`, avoiding sanitizer_common as an accidental default
  build dependency.
- Preserved SimpleOS sysroot include paths in cache-backed toolchain C/CXX
  flags so compiler-rt builtins see the staged flat libc headers and libc++
  headers even after CMake cache reuse.
- Added C11 `static_assert` exposure in SimpleOS `assert.h`, matching
  compiler-rt builtins expectations without pulling a host assert surface.
- Completed the focused x86_64 compiler-rt builtins stage and staged
  `libclang_rt.builtins-x86_64.a` into the SimpleOS Clang resource tree.
- Tightened the Clang artifact smoke with a bounded `--print-target-triple`
  probe, turning the current canonical Clang segfault into a real failure
  instead of an implicit skip.
- Added `-Wl,--defsym,__bss_end=_end` to the SimpleOS LLVM toolchain so crt0 can
  clear BSS without a full fixed-address linker script that breaks the
  host-loadable cross artifact.
- Added Linux-host fallback paths for `mmap` allocation, `write`, `exit`, and
  `fstat` after failed SimpleOS syscall probes so the canonical cross artifact
  can progress under the Linux-host smoke harness.
- Updated crt0 to preserve a conventional argc/argv/envp entry stack when one is
  present, while retaining the SimpleOS no-argument fallback for early kernels.
