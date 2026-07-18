# Desktop kernel stalls before spl_start under OVMF/GRUB boot (works under -kernel)

**Date:** 2026-07-18
**Status:** OPEN — board-runnability blocker
**Severity:** high (blocks board evidence for the glass desktop)

## Symptom

With the 4 desktop/WM evidence gates migrated from QEMU `-kernel` to real
UEFI firmware (OVMF pflash -> GRUB BOOTX64.EFI -> multiboot), the boot
chain itself is proven: `[grub-uefi] multiboot loading` and
`[BOOT64] call _start` both appear. But the gui_entry_desktop kernel then
**stalls before printing `[desktop-gui] spl_start`** (M3 lane, 60s window),
whereas the SAME kernel under `-kernel` reaches first-frame rendering
(the 12.64%+ screendump evidence). The wm_entry kernel faults post-_start
under both boot modes (pre-existing, separate).

## Why this matters

QEMU `-kernel` is QEMU acting as the bootloader; no real board boots that
way. This divergence is exactly what the board-runnable rule exists to
catch: the kernel depends on something `-kernel` provides that the real
firmware chain does not. Prime suspects, in order:

1. **Framebuffer handoff**: under `-kernel`, the kernel's VBE/BGA path
   finds a framebuffer; under UEFI, the display is GOP-owned and the
   multiboot info from GRUB may carry a different (or no) framebuffer tag.
   Early display init may spin/block waiting for VBE state that never
   arrives.
2. Multiboot info differences (memory map layout, module/cmdline tags)
   parsed before first serial output in spl_start's prologue.
3. GRUB's A20/paging/CPU state at handoff differing from QEMU's direct
   entry assumptions.

## Repro

Any migrated gate, e.g.:
`sh scripts/check/check-simpleos-x86-64-wm-qemu-readiness.shs` with
`SIMPLEOS_KERNEL_ELF` pointing at a gui_entry_desktop build — ladder
markers pass, `[desktop-gui] spl_start` absent.

## Also observed during migration (separate, minor)

- M1 (fullscreen gate): pre-existing disk-staging step builds an image too
  small for the payload — blocks its e2e run before QEMU; unrelated to
  boot mode.
- M2 (visible-display gate): e2e run timed out in the kernel *build* step
  (infra slowness), packaging chain verified independently.

## Next step

Instrument the earliest pre-spl_start path (serial putc directly in
_start/BOOT64 prologue) under OVMF boot to find the exact stall point;
then fix the framebuffer/boot-info probe to handle the UEFI/GOP case
(soft-fail to serial-only like the font path does, never spin).
