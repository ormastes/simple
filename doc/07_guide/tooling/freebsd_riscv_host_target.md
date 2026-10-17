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
