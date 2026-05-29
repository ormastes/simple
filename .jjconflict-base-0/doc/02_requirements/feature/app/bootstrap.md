# bootstrap
*Source:* `test/feature/app/bootstrap_spec.spl`

## Overview

The Simple compiler must be able to compile its own source code,
    producing an identical binary across generations.

A booted SimpleOS image must additionally be able to compile C, Rust, and
Simple sources end-to-end without a host toolchain. This is achieved by
shipping `clang`, `lld`, `libLLVM.so`, `rustc`, and `simple` as userland
binaries inside the FAT32 image, loadable by the in-OS ELF loader.

## Behavior

A compiler compiled by itself must produce identical output
        when compiling itself again.

The SimpleOS FAT32 image and initramfs may also ship a dynamic LLVM/clang/lld
        and rustc toolchain. The sysroot at `build/os/sysroot/` (IF-05)
        remains a mandatory artifact regardless of which binaries are
        ultimately baked. See `doc/04_architecture/adr/ADR-003-userland-llvm-rustc-shipment.md`
        for the override rationale and dependency chain.


