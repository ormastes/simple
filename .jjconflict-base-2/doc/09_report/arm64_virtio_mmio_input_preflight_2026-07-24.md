# ARM64 desktop input preflight report — 2026-07-24

**Status: PARTIAL / LIVE EVIDENCE PENDING**

The ARM64 desktop previously had RAMFB/Engine2D/NEON rendering but consumed
only PL011 characters.  This change wires the production QEMU `virt`
VirtIO-MMIO input transport in the ARM64 runtime and routes records through the
shared VirtIO input translators.  It does not claim a live QEMU pass.

| Requirement | Current evidence |
| --- | --- |
| Device discovery | Scans all 32 ARM `virt` MMIO slots and accepts ID 18 only after keyboard/pointer capability checks. |
| Event transport | Bounded reset, accumulated status, stale QueueReady rejection, validated DMA shape, modern eventq 0, 32 writable records, acquire/release ordered drain/recycle, exact-length enforcement. |
| Shared event model | `virtio_input_key_event` and `VirtioMouseAccum`; no ARM-only key/mouse model. |
| QEMU attachment | Both canonical ARM64 target definitions add MMIO keyboard and mouse devices. |
| SIMD/render path | Existing entry still rejects zero AArch64 NEON fill receipts before input admission. |
| Live input/capture | Not run: host-first gate remains active.  System contract is fail-closed pending QMP correlation and RAMFB capture. |

Keyboard press and release each carry device/poll/state/frame markers. Pointer
REL/button records retain one guest sequence through `SYN_REPORT`, then emit
`[wm-pointer-poll] source=poll`, state, and later frame markers. No IRQ claim is
made for the polling implementation. Theme toggle reports a blocker instead
of silently passing.

## Commands run

```text
clang --target=aarch64-none-elf -ffreestanding -fsyntax-only examples/09_embedded/simple_os/arch/arm64/boot/baremetal_stubs.c
# PASS

sh scripts/check/check-arm64-virtio-input-preflight.shs
# PASS; includes focused host C contract plus ARM64 syntax, launches no QEMU

SIMPLE_LIB=src /Users/ormastes/simple/src/compiler_rust/target/bootstrap/simple os build --scenario=arm64-desktop-engine2d
# BLOCKED before entry compilation: missing bin/release/aarch64-unknown-simpleos/simple
```

The latter used the Rust bootstrap driver only as a diagnostic because this
isolated worktree has no current self-hosted ARM payload.  It did not launch
QEMU.  The next allowed validation is a fresh self-hosted ARM payload build,
then exactly one QMP capture attempt after the host evidence gate is green.
