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
| Focused x86_64 `bin/lld` cross executable link | FAIL | `ninja -C build/os/llvm/cross-x86_64-unknown-simpleos bin/lld` -> all requested LLD/LLVM objects and static archives build, final executable link is reached, and runtime archives are linked after LLVM archives; remaining failures are missing ABI/libc++/libm entry points |
| Cross-build plan scaffolding | PASS | `SIMPLE_LIB=src bin/simple test test/02_integration/os/port/llvm/cross_build_plan_spec.spl --mode=interpreter --clean` -> 18 examples, 0 failures |
| Per-target compiler-rt/build staging scaffolding | PASS | `SIMPLE_LIB=src bin/simple test test/02_integration/os/port/llvm/per_target_build_spec.spl --mode=interpreter --clean` -> 43 examples, 0 failures |
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
| SimpleOS libc rebuild | PASS | `make -C src/os/libc` -> rebuilt `libsimpleos_c.a` including `simpleos_utsname.o` |
| SimpleOS C++/POSIX surface probes | PASS | `clang++ --target=x86_64-unknown-simpleos --sysroot=build/os/sysroot ...` including `<string>`, `<mutex>`, `<shared_mutex>`, `<future>`, `<random>`, `gethostname`, `getsid`, `std::isxdigit`, `sys/resource.h`, `sys/socket.h`, `sys/un.h`, `sys/wait.h`, `pwd.h`, `alarm`, `setsid`, `getpagesize`, and signal flags compiles |
| Cross clang artifact-gated smoke | PASS | `SIMPLE_LIB=src bin/simple test test/02_integration/os/port/llvm/smoke_clang_spec.spl --mode=interpreter --clean` -> 5 examples, 0 failures |

## Current Blocker

The canonical cross clang artifact is not present at
`build/os/llvm/cross-x86_64-unknown-simpleos/bin/clang`
(`test -f ...` exit code 1). Host tblgen tools exist, libc++ headers and a
minimal libc++ runtime archive are staged into the SimpleOS sysroot, and the
focused x86_64 LLD build now reaches the final `bin/lld` executable link.

The previous missing-symbol class for libc++ headers, pthread condition
variables, `strerror_r`, and wide numeric conversion functions is cleared.
The latest final-link probe fails on the next ABI/runtime surface:

```text
undefined symbol: main
undefined symbol: operator new(unsigned long, std::align_val_t)
undefined symbol: operator delete(void*, unsigned long, std::align_val_t)
undefined symbol: operator new(unsigned long, std::nothrow_t const&)
undefined symbol: std::__...::locale::locale()
undefined symbol: std::__...::ctype<char>::id
undefined symbol: std::__...::collate<char>::id
undefined symbol: __cxa_thread_atexit
undefined symbol: vfprintf
undefined symbol: wmemcmp
undefined symbol: erf
undefined symbol: logb
undefined symbol: rint
```

The relocation failures from PIE-style linking are cleared by forwarding
`-Wl,-no-pie` through the SimpleOS LLVM toolchain. The next focused work should
add the smallest owned runtime/ABI surface for aligned and nothrow allocation,
thread-local destructors, missing stdio/wide/m lib functions, and either
SimpleOS C++ entry handling or an upstream target hook so C++ `main` resolves
for SimpleOS executables.

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
