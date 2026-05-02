# SimpleOS ARM Embedded-Asm Migration - 2026-04-21

## Status
- QEMU media now uses distinct per-platform FAT32 image names from the
  SimpleOS platform catalog.
- `scripts/make_os_disk.shs` can populate FAT32 images without mtools or loop
  mount by using its Python 8.3 FAT32 writer fallback.
- ARM64 and ARM32 SMF/FAT32 scenarios now reach native-build with populated
  media, but this checkout's selected Simple compiler was not built with the
  Rust `llvm` feature.

## Remaining Work
- Rebuild the selected Simple compiler with LLVM enabled and LLVM 18 available.
- Re-run:
  - `SIMPLE_ALLOW_FREESTANDING_STUBS=1 SIMPLE_OS_BUILD_TIMEOUT_MS=240000 bin/simple os test --scenario=arm64-virtio-fat32-smf`
  - `SIMPLE_ALLOW_FREESTANDING_STUBS=1 SIMPLE_OS_BUILD_TIMEOUT_MS=240000 bin/simple os test --scenario=arm32-virtio-fat32-smf`
- After live ARM parity is green, migrate boot-critical ARM C helpers from
  `examples/simple_os/arch/arm64/boot/baremetal_stubs.c` and
  `examples/simple_os/arch/arm32/boot/baremetal_stubs.c` into Simple modules
  with embedded asm for system-register and wait/barrier instructions.
- Keep linker scripts and minimal `crt0.S`/`crt0.s` entry trampolines until the
  Simple compiler can prove equivalent entry generation.

## Blocker Evidence
- ARM64 and ARM32 both fail native-build with:
  `LLVM backend requested but 'llvm' feature not enabled`.
