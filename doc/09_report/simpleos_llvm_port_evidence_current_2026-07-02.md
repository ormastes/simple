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
| Sysroot libc++ header staging | PASS | `sh src/os/port/llvm/sysroot.shs` -> staged libc++ under `build/os/sysroot/include/c++/v1`, generated `__config_site`, installed `__assertion_handler`; header count 1847 |
| x86_64 cross LLVM configure | PASS | `SIMPLEOS_TARGET_TRIPLE=x86_64-unknown-simpleos SIMPLE_TARGET=x86_64-unknown-simpleos sh src/os/port/llvm/build.shs cross` -> CMake configure/generate complete; build enters LLVM object compilation |
| x86_64 cross LLVM object build | FAIL | same command after regenerating/continuing the x86_64 build dir -> `LLVM_ON_UNIX` is defined; libc++ `std::wstring`, mutex, shared mutex, future, and `std::random_device` declarations are visible; POSIX process/signal/socket/userdb gaps from the prior run are cleared; `raw_os_ostream.cpp`, `Path.cpp`, `AssignmentTrackingAnalysis.cpp`, `MIRFSDiscriminator.cpp`, `MIRSampleProfile.cpp`, `InstrOrderFile.cpp`, `AddressSanitizer.cpp`, `MemProfContextDisambiguation.cpp`, `ImportedFunctionsInliningStatistics.cpp`, `MCPseudoProbe.cpp`, and `MCParser/AsmParser.cpp` compile; `lib/libLLVMSupport.a` links; build reaches LLVM MC/MCParser object wave 33/1809 before the current blocker |
| Cross-build plan scaffolding | PASS | `SIMPLE_LIB=src bin/simple test test/02_integration/os/port/llvm/cross_build_plan_spec.spl --mode=interpreter --clean` -> 18 examples, 0 failures |
| Per-target compiler-rt/build staging scaffolding | PASS | `SIMPLE_LIB=src bin/simple test test/02_integration/os/port/llvm/per_target_build_spec.spl --mode=interpreter --clean` -> 39 examples, 0 failures |
| Focused `Path.cpp` compile | PASS | direct clang++ compile with Ninja flags plus `-D__simpleos__=1` -> object builds; only existing futimes/futimens warning remains |
| Focused `AssignmentTrackingAnalysis.cpp` compile | PASS | direct clang++ compile with Ninja flags after replacing `std::stringstream` with `raw_string_ostream` -> object builds |
| Focused `MIRFSDiscriminator.cpp` compile | PASS | direct clang++ compile with Ninja flags after replacing `SampleProf.h` `std::ostringstream` use with `raw_string_ostream` -> object builds |
| Focused instrumentation hex compile | PASS | direct clang++ compile with Ninja flags for `InstrOrderFile.cpp` and `AddressSanitizer.cpp` after replacing iostream/iomanip hex formatting with `utohexstr` -> objects build |
| Focused `MemProfContextDisambiguation.cpp` compile | PASS | direct clang++ compile with Ninja flags after replacing iostream node id formatting with `Twine::utohexstr` -> object builds |
| Focused `ImportedFunctionsInliningStatistics.cpp` compile | PASS | direct clang++ compile with Ninja flags after replacing `stringstream` / `setprecision` with `raw_string_ostream` and LLVM `format("%.4g", ...)` -> object builds |
| Focused LLVM MC no-sstream compile | PASS | direct clang++ compile with Ninja flags for `MCPseudoProbe.cpp`, `MCParser/AsmParser.cpp`, and `MCParser/MasmParser.cpp` after replacing `std::ostringstream` with `raw_string_ostream` -> objects build |
| SimpleOS libc rebuild | PASS | `make -C src/os/libc` -> rebuilt `libsimpleos_c.a`; existing `SIZE_MAX` macro warning remains |
| SimpleOS C++/POSIX surface probes | PASS | `clang++ --target=x86_64-unknown-simpleos --sysroot=build/os/sysroot ...` including `<string>`, `<mutex>`, `<shared_mutex>`, `<future>`, `<random>`, `gethostname`, `getsid`, `std::isxdigit`, `sys/resource.h`, `sys/socket.h`, `sys/un.h`, `sys/wait.h`, `pwd.h`, `alarm`, `setsid`, `getpagesize`, and signal flags compiles |
| Cross clang artifact-gated smoke | PASS | `SIMPLE_LIB=src bin/simple test test/02_integration/os/port/llvm/smoke_clang_spec.spl --mode=interpreter --clean` -> 5 examples, 0 failures |

## Current Blocker

The canonical cross clang artifact is not present at
`build/os/llvm/cross-x86_64-unknown-simpleos/bin/clang`
(`test -f ...` exit code 1). Host tblgen tools now exist, libc++ headers are
staged into the SimpleOS sysroot, and the x86_64 cross stage now gets through
CMake configure/generate into object compilation.

```text
MasmParser.cpp: implicit instantiation of undefined template
'std::basic_ostringstream<char>'
```

The remaining blocker class is now libc++ no-localization iostream coverage in
later LLVM objects, not LLVM Support/POSIX bring-up. `Path.cpp` clears and
`lib/libLLVMSupport.a` links. After the last build probe, LLVM MC formatting in
`MCParser/MasmParser.cpp` was patched to use `raw_string_ostream`; the next
cross-build probe should validate whether that clears the current MC parser
object wave or exposes the next no-localization iostream use.

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
