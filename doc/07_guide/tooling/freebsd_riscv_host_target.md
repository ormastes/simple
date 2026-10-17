# Native RISC-V FreeBSD bootstrap target detection

The Stage 3 provenance host resolver recognizes the native FreeBSD RISC-V
host as `riscv64gc-unknown-freebsd`, matching Rust's native target triple.
FreeBSD 14.4 reports the machine family as `uname -m = riscv` and the
processor as `uname -p = riscv64`. The resolver checks the processor for
that family rather than treating `riscv` as a complete target identity.
An explicit `uname -m = riscv64` is also accepted. Unknown, unavailable or
32-bit processor results fail closed; existing amd64 and arm64 routes remain.

The focused regression test is:

```sh
sh test/01_unit/scripts/freebsd_riscv_host_platform_test.shs
```

It covers the FreeBSD machine/processor forms, unsupported and unavailable
processor results, and existing FreeBSD and Linux host routes. A real-guest
integration check additionally sources the resolver and compares its result
with the `host:` field of `rustc -vV`.

This fix only enables native host identity resolution. It does not add a
RISC-V guest route to the QEMU wrapper, install LLVM, qualify a compiler, or
prove a Stage 3 bootstrap. Continue using the native FreeBSD checker after
its actual toolchain prerequisites have been satisfied. RISC-V provisioning
and toolchain evidence is recorded in
`doc/08_tracking/bug/freebsd_riscv64_binary_toolchain_repository_20261018.md`.
