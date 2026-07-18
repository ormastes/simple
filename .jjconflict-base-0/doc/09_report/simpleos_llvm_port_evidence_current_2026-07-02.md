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
| Per-target compiler-rt/build staging scaffolding | PASS | `SIMPLE_LIB=src bin/simple test --no-session-daemon test/02_integration/os/port/llvm/per_target_build_spec.spl --mode=interpreter --clean` -> 59 examples, 0 failures; includes the `build.shs` target-marker guard that rebuilds the shared sysroot when `share/simpleos/target-triple.txt` does not match the requested triple for `cross` or direct `compiler-rt` stages |
| Focused x86_64 compiler-rt builtins configure | PASS | `SIMPLEOS_TARGET_TRIPLE=x86_64-unknown-simpleos sh src/os/port/llvm/build.shs compiler-rt` now gets past CMake configure after removing the contradictory `COMPILER_RT_DEFAULT_TARGET_TRIPLE` flag and stale empty `CMAKE_*_FLAGS` cache values |
| Focused x86_64 compiler-rt builtins compile/stage | PASS | `SIMPLEOS_TARGET_TRIPLE=x86_64-unknown-simpleos sh src/os/port/llvm/build.shs compiler-rt` -> `builtins` builds 165/165 and stages `libclang_rt.builtins-x86_64.a` under `build/os/sysroot/lib/clang/20/lib/x86_64-unknown-simpleos/`; staged archive is 236626 bytes |
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
| Cross clang target-triple host smoke | PASS | `timeout 5s build/os/llvm/cross-x86_64-unknown-simpleos/bin/clang --print-target-triple` -> exit 0, stdout `x86_64-unknown-simpleos` |
| Cross clang compile host smoke | PASS | `timeout 10s build/os/llvm/cross-x86_64-unknown-simpleos/bin/clang --target=x86_64-unknown-simpleos -c examples/09_embedded/simpleos_hello_c/hello.c -o /tmp/smoke_clang_hello.o` -> exit 0, object 1056 bytes |
| Cross object-tool smoke | PASS | `build/os/llvm/cross-x86_64-unknown-simpleos/bin/llvm-nm /tmp/smoke_clang_hello.o` -> exit 0, `0000000000000000 T main`; fresh `timeout 10s .../bin/ld.lld -T build/os/sysroot/share/simpleos/simpleos.ld build/os/sysroot/lib/crt0.o /tmp/smoke_clang_hello.o -L build/os/sysroot/lib -lsimpleos_c -o /tmp/smoke_clang_hello.elf` -> exit 0, ELF 39144 bytes |
| Cross clang artifact-gated smoke | PASS | `SIMPLEOS_TARGET_TRIPLE=x86_64-unknown-simpleos sh src/os/port/llvm/sysroot.shs`; then `SIMPLE_LIB=src bin/simple test --no-session-daemon test/02_integration/os/port/llvm/smoke_clang_spec.spl --mode=interpreter --clean` -> 8 examples, 0 failures: canonical x86_64 artifact exists, target triple prints, hello.c compiles, `llvm-nm` finds `main`, `ld.lld` links a SimpleOS ELF including overwrite of an existing output, canonical `clang hello.c -o hello.elf` drives cc1 plus lld successfully, a `__int128` division probe links through staged compiler-rt builtins, and the aarch64 stage-2 artifacts plus seeded builtins archive are present. The link scenarios assert `build/os/sysroot/share/simpleos/target-triple.txt` is `x86_64-unknown-simpleos` before using the shared sysroot. |
| Cross clang driver link smoke | PASS | `timeout 20s build/os/llvm/cross-x86_64-unknown-simpleos/bin/clang --target=x86_64-unknown-simpleos examples/09_embedded/simpleos_hello_c/hello.c -o /tmp/smoke_clang_driver_hello.elf` -> exit 0, ELF 39144 bytes |
| aarch64 sysroot libc++ runtime staging | PASS | `SIMPLEOS_TARGET_TRIPLE=aarch64-unknown-simpleos sh src/os/port/llvm/sysroot.shs` -> installed 1851 headers, built and staged `libc++.a`, `crt0.o`, `libsimpleos_c.a`, `libm.a`, and linker script for the aarch64 SimpleOS sysroot |
| aarch64 TargetParser `Host.cpp` compile | PASS | `ninja -C build/os/llvm/cross-aarch64-unknown-simpleos lib/TargetParser/CMakeFiles/LLVMTargetParser.dir/Host.cpp.o` -> object builds after guarding the Linux BPF `syscall(...)` probe for `__simpleos__` |
| aarch64 AArch64 frame-helper compile | PASS | `ninja -C build/os/llvm/cross-aarch64-unknown-simpleos lib/Target/AArch64/CMakeFiles/LLVMAArch64CodeGen.dir/AArch64LowerHomogeneousPrologEpilog.cpp.o` -> object builds after replacing local `std::ostringstream` helper-name formatting with `raw_string_ostream` |
| aarch64 target sysroot archives | PASS | `SIMPLEOS_TARGET_TRIPLE=aarch64-unknown-simpleos SIMPLE_TARGET=aarch64-unknown-simpleos sh src/os/port/llvm/sysroot.shs` -> stages target-correct `crt0.o`, `libsimpleos_c.a`, `libm.a`, `libc++.a`, and `libclang_rt.builtins-aarch64.a`; `file` confirms `crt0.o`, `simpleos_libc.o`, and generated syscall objects are ELF64 AArch64 |
| aarch64 cross LLVM stage 2 | PASS | `SIMPLEOS_TARGET_TRIPLE=aarch64-unknown-simpleos SIMPLE_TARGET=aarch64-unknown-simpleos sh src/os/port/llvm/build.shs cross` -> completed 2526/2526 and produced cross-compiled `bin/clang-20`, `bin/clang`, and `bin/lld` under `build/os/llvm/cross-aarch64-unknown-simpleos` |

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
`clang-20`. Host-running it now prints `x86_64-unknown-simpleos`, compiles the
`hello.c` smoke object, runs `llvm-nm` on the object, and links a fresh
SimpleOS ELF with `ld.lld`. The canonical clang driver also now compiles and
links `hello.c` directly through its cc1 subprocess and SimpleOS `ld.lld`
toolchain job, and resolves a compiler-rt builtins user from the staged Clang
20 resource directory.

This session cleared the earlier `_start` BSS crash with `__bss_end=_end`,
added Linux-host fallback paths for constructor allocation, `write`, `exit`,
`_Exit`, `stat`/`fstat`, `open`, `read`, `close`, `lseek`, `ftruncate`,
`mmap`, `munmap`, `mprotect`, `pipe`, `dup`, `dup2`, `fork`, `execve`, and
`waitpid`, preserved host argc/argv/envp in crt0, added `-Wl,--export-dynamic`
plus cache reset for host-loadable cross tools, aligned compiler-rt staging to
Clang 20 resource dirs, gave the SimpleOS Clang toolchain a default sysroot and
runtime link paths, and added an explicit Clang driver `llvm::outs().flush()`
for small target-triple outputs.

The aarch64 target-side LLVM stage 2 now completes. This session cleared the
earlier flat `endian.h`, target `CHAR_MIN`/`CHAR_MAX`, `sys/vfs.h`,
`RLIMIT_DATA`/`RLIMIT_CORE`, TargetParser `syscall(...)`, and AArch64
`std::ostringstream` blockers, then fixed the target-link frontier by forcing
`--target=aarch64-unknown-simpleos` through CMake cache flags and selecting the
`aarch64elf` LLD emulation instead of the host default `elf_x86_64` mode.

The aarch64 sysroot is now target-correct enough for the full cross build:
`crt0.o`, `libsimpleos_c.a`, and `libm.a` are rebuilt from aarch64 objects;
`setjmp` / `longjmp` and `__clear_cache` are provided by generated aarch64
runtime assembly; and `libclang_rt.builtins-aarch64.a` is seeded into the
sysroot so long-double helper references such as `__extenddftf2` and `__lttf2`
resolve during the target-side `bin/lld` and `bin/clang` links.

Compiler-rt staging has advanced through x86_64 builtins compile and archive
staging. Broader target rollout and resource-dir integration remain gated on
repeating the now-green canonical compile/nm/link smoke for non-x86_64 targets.

The shared sysroot can be restaged for different targets during this lane. The
x86_64 smoke now fails early on a target-marker mismatch instead of reaching
opaque `ld.lld` architecture errors when `crt0.o` or staged archives were last
written by another target.

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
  `libclang_rt.builtins-x86_64.a` into the SimpleOS Clang 20 resource tree.
- Tightened the Clang artifact smoke with a bounded `--print-target-triple`
  probe, turning the current canonical Clang segfault into a real failure
  instead of an implicit skip.
- Added `-Wl,--defsym,__bss_end=_end` to the SimpleOS LLVM toolchain so crt0 can
  clear BSS without a full fixed-address linker script that breaks the
  host-loadable cross artifact.
- Added `-Wl,--export-dynamic` to the SimpleOS LLVM toolchain and unset stale
  `CMAKE_EXE_LINKER_FLAGS` during cross configure so rebuilt object tools expose
  the dynamic metadata needed by the Linux host loader.
- Added Linux-host fallback paths for `mmap` allocation, `write`, `exit`, and
  `fstat` after failed SimpleOS syscall probes so the canonical cross artifact
  can progress under the Linux-host smoke harness.
- Updated crt0 to preserve a conventional argc/argv/envp entry stack when one is
  present, while retaining the SimpleOS no-argument fallback for early kernels.
- Guarded crt0 BSS clearing when weak host-smoke symbols leave `__bss_end`
  before `__bss_start`, preventing a backwards clear during host-loaded tools.
- Added Linux-host fallback paths for SimpleOS libc `stat`, `open`, `read`,
  `close`, and `lseek` so canonical Clang host-smoke probes can read config
  files and source inputs.
- Added Linux-host fallback paths for SimpleOS libc `_Exit`, `ftruncate`,
  `mmap`, `munmap`, and `mprotect` so `llvm-nm` and fresh-output `ld.lld` can
  complete the object-tool smoke.
- Added Linux-host fallback paths for SimpleOS libc `pipe`, `dup`, `dup2`,
  `fork`, `execve`, and `waitpid` so the Clang driver can spawn its cc1
  subprocess during host-smoke runs.
- Updated compiler-rt resource-dir staging from Clang 19 to Clang 20 and
  recorded the SimpleOS Clang toolchain default-sysroot patch for driver
  compile-and-link.
- Updated the smoke spec to expect the normalized `x86_64-unknown-simpleos`
  target triple used by the current cross-build plan and toolchain.
- Updated the smoke spec to create a stale output ELF before invoking
  `ld.lld`, proving the no-async-unlink patch handles overwrite without a
  pthread-backed `std::thread`.
- Recorded and applied the Clang driver target-triple flush patch for small
  `llvm::outs()` outputs in the freestanding cross artifact.
- Recorded and applied the LLD filesystem patch that avoids async unlink when
  `LLVM_ENABLE_THREADS=OFF`, so overwriting an existing output no longer
  requires pthread-backed `std::thread`.
- Added the flat SimpleOS `endian.h` wrapper required by LLVM support headers
  and made `CHAR_MIN` / `CHAR_MAX` follow `__CHAR_UNSIGNED__` so aarch64 libc++
  sources compile with unsigned plain `char`.
- Added the SimpleOS `sys/vfs.h` compatibility wrapper over `statvfs`, exposed
  `f_type`, and broadened `getrlimit` / `setrlimit` stubs to accept
  `RLIMIT_DATA` and `RLIMIT_CORE`, moving the aarch64 cross build frontier to
  the LLVM TargetParser `syscall(...)` BPF probe.
- Recorded and applied the LLVM TargetParser patch that sends SimpleOS through
  the generic BPF CPU-name path instead of calling raw Linux `syscall(...)`.
- Recorded and applied the AArch64 backend patch that replaces local
  `std::ostringstream` frame-helper name formatting with LLVM
  `raw_string_ostream`.
- Forced `CMAKE_C_COMPILER_TARGET`, `CMAKE_CXX_COMPILER_TARGET`, and
  `CMAKE_ASM_COMPILER_TARGET` plus cached `--target=<triple>` flags in the
  SimpleOS LLVM CMake toolchain, moving the aarch64 frontier from mixed
  x86_64/aarch64 objects to the remaining host-linker emulation selection.
- Added per-target LLD emulation selection in the SimpleOS LLVM CMake
  toolchain, clearing the host `collect2` / `elf_x86_64` link mode for
  aarch64 SimpleOS objects.
- Added aarch64 sysroot runtime generation for SimpleOS libc, crt0,
  `setjmp` / `longjmp`, and `__clear_cache`, avoiding x86_64 archive reuse in
  target-side aarch64 links.
- Seeded `libclang_rt.builtins-aarch64.a` into the SimpleOS sysroot from an
  available bare-metal compiler-rt archive or aarch64 libgcc fallback.
- Completed the full aarch64 SimpleOS LLVM stage 2 cross build through
  `bin/lld` and `bin/clang`.
