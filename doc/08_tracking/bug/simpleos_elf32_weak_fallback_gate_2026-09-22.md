# SimpleOS ELF32 weak fallback gate

The reviewed source fix limits the weak fallback to supported legacy boot
paths and fails an explicitly requested ELF32 wrap instead of silently
publishing a malformed kernel. Focused fixture coverage accompanies the gate.

## Deferred environment TODO

TODO: after the Linux bootstrap publishes an admitted self-hosted compiler,
run `sh scripts/check/check-simpleos-x86-kernel-elf.shs` against the produced
ELF32 and ELF64 kernels, then run
`sh scripts/check/check-simpleos-bootstrap-qemu.shs --full`. Retain the exact
kernel digest and QEMU boot receipt; source and fixture review alone do not
close the platform acceptance row.
