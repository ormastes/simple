# ARM64 desktop input preflight report — 2026-07-24

**Status: PARTIAL / LIVE EVIDENCE PENDING**

The ARM64 desktop previously had RAMFB/Engine2D/NEON rendering but consumed
only PL011 characters.  This change wires the production QEMU `virt`
VirtIO-MMIO input transport in the ARM64 runtime and routes records through the
shared VirtIO input translators.  It does not claim a live QEMU pass.

| Requirement | Current evidence |
| --- | --- |
| Device discovery | Scans all 32 ARM `virt` MMIO slots and accepts ID 18 only after keyboard/pointer capability checks. |
| Event transport | Modern eventq 0 setup, 32 writable eight-byte records, used-ring drain/recycle, IRQ acknowledgement. |
| Shared event model | `virtio_input_key_event` and `VirtioMouseAccum`; no ARM-only key/mouse model. |
| QEMU attachment | Both canonical ARM64 target definitions add MMIO keyboard and mouse devices. |
| SIMD/render path | Existing entry still rejects zero AArch64 NEON fill receipts before input admission. |
| Live input/capture | Not run: host-first gate remains active.  System contract is fail-closed pending QMP correlation and RAMFB capture. |

## Commands run

```text
clang --target=aarch64-none-elf -ffreestanding -fsyntax-only examples/09_embedded/simple_os/arch/arm64/boot/baremetal_stubs.c
# PASS

SIMPLE_LIB=src /Users/ormastes/simple/src/compiler_rust/target/bootstrap/simple os build --scenario=arm64-desktop-engine2d
# BLOCKED before entry compilation: missing bin/release/aarch64-unknown-simpleos/simple
```

The latter used the Rust bootstrap driver only as a diagnostic because this
isolated worktree has no current self-hosted ARM payload.  It did not launch
QEMU.  The next allowed validation is a fresh self-hosted ARM payload build,
then exactly one QMP capture attempt after the host evidence gate is green.
