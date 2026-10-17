# Native RISC-V FreeBSD bootstrap target detection

The Stage 3 provenance host resolver recognizes the native FreeBSD RISC-V
host as `riscv64-unknown-freebsd`, matching Simple's native artifact paths.
The shared platform detector exports that value as `PLATFORM_TRIPLE` and
the Cargo spelling `riscv64gc-unknown-freebsd` as `PLATFORM_RUST_TRIPLE`.
FreeBSD 14.4 reports the machine family as `uname -m = riscv` and the
processor as `uname -p = riscv64`. The resolver checks the processor for
that family rather than treating `riscv` as a complete target identity.
An explicit `uname -m = riscv64` is also accepted. Unknown, unavailable or
32-bit processor results fail closed; existing amd64 and arm64 routes remain.

The focused regression test is:

```sh
sh test/01_unit/scripts/freebsd_riscv_host_platform_test.shs
sh test/01_unit/scripts/freebsd_riscv_target_alignment_test.shs
```

It covers the FreeBSD machine/processor forms, unsupported and unavailable
processor results, and existing FreeBSD and Linux host routes. A real-guest
integration check compares the provenance resolver with `PLATFORM_TRIPLE`,
then compares `PLATFORM_RUST_TRIPLE` with the `host:` field of `rustc -vV`.
Do not use Cargo's spelling for Simple Stage 2/3 output directories.

The admitted LLVM patch versions are defined in the shared platform detector.
At this revision native FreeBSD admits 23.1.1 and 23.1.2. A newer ports recipe
alone does not admit 23.1.3 for bootstrap; check admission before building a
toolchain rather than relaxing the gate to fit an available archive.

This fix only enables native host identity resolution. It does not add a
RISC-V guest route to the QEMU wrapper, install LLVM, qualify a compiler, or
prove a Stage 3 bootstrap. Continue using the native FreeBSD checker after
its actual toolchain prerequisites have been satisfied. RISC-V provisioning
and toolchain evidence is recorded in
`doc/08_tracking/bug/freebsd_riscv64_binary_toolchain_repository_20261018.md`.

## Cross-built LLVM qualification

An admitted LLVM 23.1.2 toolchain has now passed native compilation and execution
inside the FreeBSD 14.4 RISC-V guest. This qualifies the toolchain, not Simple's
bootstrap. The execution plan records its archive identity and remaining gates:
`doc/03_plan/riscv_freebsd_bootstrap_20261017.md`.

When reproducing the Linux-to-FreeBSD LLVM build, configure LLD for all three
CMake link categories: `CMAKE_EXE_LINKER_FLAGS`,
`CMAKE_SHARED_LINKER_FLAGS` and `CMAKE_MODULE_LINKER_FLAGS`. Each needs
`-fuse-ld=lld`. Omitting module flags leaves Clang plugin links using the host
x86 linker, which rejects the RISC-V `elf64lriscv` emulation. Resume the cached
build after correcting that flag; rebuilding compiler objects is unnecessary.

Extract the verified archive as the guest installer with
`tar --no-same-owner -xzf <archive> -C /`, then add
`/usr/local/llvm23/lib` through `ldconfig -m`. Preserving Linux user ownership
causes FreeBSD's loader cache to ignore the library directory. Require both
`llvm-config --version` admission and an executed guest Clang output before
proceeding to the canonical native bootstrap checker.

## Source prerequisites and GNU Make binding

Selecting `gmake` at the top level does not bind every recursive build to it.
The Perl 5.42.3 Encode makefile selected `MAKE = make`; FreeBSD's BSD make
then rejected GNU Make 4.4.1 jobserver flags with `to option '-j' must be a
positive number`. An isolated native fixture reproduced this failure and
passed when the command-line `MAKE` override selected GNU Make explicitly.

For the cached Perl build, resume with:

```sh
gmake -j 2 MAKE=/usr/local/bin/gmake
gmake MAKE=/usr/local/bin/gmake install
```

Wait for all jobs from the failed invocation to finish before resuming, so
generated Unicode tables and compiled objects remain reusable. This proves
the make-binding repair mechanism; require successful installation and an
executed installed Perl probe before admitting the full prerequisite stage.

CMake 3.31.12 was built against the qualified guest sysroot on Linux and
then qualified inside FreeBSD by configuring a C/C++ project with Clang
23.1.2, compiling it and executing output `42`. Install only after that native
test passes. The installed `cmake`, `ctest` and `cpack` version checks passed.
Cross-build success or `--version` alone is insufficient qualification.

## Guest temporary-file retention

The persistent guest uses native daily `periodic` maintenance. Configure
`/etc/periodic.conf` with `daily_clean_tmps_enable="YES"`,
`daily_clean_tmps_dirs="/tmp"`, `daily_clean_tmps_days="7"` and
`daily_clean_tmps_verbose="YES"`. Confirm cron is enabled/running and
`/etc/crontab` schedules `periodic daily`.

The native cleaner requires access, modification and change ages all to exceed
seven days and retains its default exclusions. Keep source, toolchain caches
and bootstrap evidence outside `/tmp`; this guest stores them under `/root`.
This policy does not delete host overlays or worktree recovery archives, and
does not establish that the repository QEMU cleanup helper is safe to run.
Reboot-and-reconnect verification remains a separate acceptance gate.
