# Desktop kernel stalls before spl_start under OVMF/GRUB boot (works under -kernel)

**Date:** 2026-07-18
**Status:** RESOLVED — not reproducible on current committed source (see Findings); remaining blocker is the shared first-frame heap exhaustion, tracked separately
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

## Findings — OVMF-STALL lane (2026-07-18)

**Resolution: NOT REPRODUCIBLE on current committed source. The filed symptom
(stall/fault before `[desktop-gui] spl_start` under OVMF) no longer occurs, and
there is NO OVMF-vs-`-kernel` divergence in the current binary. The prime suspect
(framebuffer probe) is disproved. The real remaining blocker to a rendered
desktop is a SHARED, boot-mode-independent heap-exhaustion panic — see below.**

### The captured log was a FAULT (not a stall), from a stale binary

The OVMF serial log this bug was filed from showed a fault cascade, not a hang:

```
[BOOT64] call _start
FAULT @ 0x000000000000101f
FAULT @ 0x0000000001948480
```

crt0's `_fault_handler` (examples/09_embedded/simple_os/arch/x86_64/boot/crt0.s)
is a test-harness recovery stub — on a fault it advances RIP by 2 and returns nil
in RAX, which on a *real* fault manufactures a cascade. So the two FAULT lines are
one real fault plus corrupted wandering. That log was produced by an older/stale
kernel build (01:55), predating the working build (03:55), and/or a different
entry (the wm_entry class this doc already notes faults post-_start under BOTH
boot modes). It does not reflect the current gui_entry_desktop binary.

### Current behavior — verified identical under BOTH boot modes

Boot-critical sources are clean in `jj diff` and predate the build: `crt0.s`,
`gui_entry_desktop.spl`, `linker.ld` (links at 0x08000000 / 128MB, entry
`_entry32`=0x0800001c), `com1_common.spl`, `console.spl`. Verified with the
committed-boot-source build `build/os/_wklast/desktop.elf`.

Under BOTH OVMF (OVMF pflash -> GRUB BOOTX64.EFI -> multiboot) and QEMU `-kernel`,
the kernel reaches `[desktop-gui] spl_start` and proceeds IDENTICALLY through the
entire init: arch bootstrap, MMIO, PMM, VMM, memory-bootstrap, VFS, pkg,
framebuffer init, scanout-evidence, keyboard, mouse, font fallback, compositor,
shell, three app spawns, launcher, `[dbg-vbe] pre-first-frame`.

The migrated gate now PASSES under OVMF —
`check-simpleos-x86-64-wm-qemu-readiness.shs` with `SIMPLEOS_KERNEL_ELF` set
reports `status: ready`, `boot_verified: true`, `grub_efi_ran: true`,
`kernel_start_reached: true`.

### Framebuffer BAR differs but causes NO divergence (prime suspect disproved)

- `-kernel`: scanout address = 0xFD000000 (PCI hole below 4GB)
- OVMF: scanout address = 0x80000000 (OVMF's PCI enumeration relocates the BAR)

Despite the different BAR, `_vram_mapping_probe`'s direct write+readback is
BYTE-IDENTICAL in both modes (wrote 0x7A7B7C7F, read 0x7A7B7C78 in both — a benign
std-vga low-bit artifact, not a mapping fault). Both modes then reach the same
downstream state. The framebuffer handoff is not the problem, and the kernel
probes the BGA/std-vga hardware directly (it does not read the multiboot
framebuffer tag), so it does not depend on `-kernel`-provided VBE state.

### The real remaining blocker (SHARED, not a boot-mode divergence)

Both modes end at the SAME panic inside `render_baremetal_first_frame`
(gui_entry_desktop.spl line 428):

```
[PANIC] heap exhausted
[PANIC] heap_off=0xbfffff0 req=0x20 limit=0xc000000
```

The renderer allocates repeated 8MB (0x800020) chunks via `rt_array_repeat`
(caller 0x8010776 -> symbol `rt_array_repeat`) until the 192MB (0xc000000) heap is
exhausted — same offset, caller, and limit under both `-kernel` and OVMF. This
blocks `[desktop-gui] desktop-ready` on BOTH boot paths equally, so it is NOT a
board-runnability divergence. The identical repeated caller+size points to a
per-frame/per-widget array leak, so enlarging the heap would only defer it.
=> Track as a SEPARATE renderer/heap bug.

### GRUB cosmetic note (not causal)

GRUB prints `error: no suitable video mode found.` +
`WARNING: no console will be available to OS`. The migrated grub.cfg uses a bare
`multiboot /boot/kernel.elf` with no `insmod all_video` / `set gfxpayload`. This
is cosmetic — the kernel reaches spl_start and framebuffer init fine without a
GRUB framebuffer tag and does not hang when it is absent. Adding
`insmod all_video` + `set gfxpayload=keep` to the harness grub.cfg would silence
the messages but change no kernel behavior; left out to avoid scope creep.

### Actions / no source changes

No source changes were required — the pre-spl_start fault is already resolved in
the committed tree; the divergence hypothesis was disproved by comparing OVMF and
`-kernel` serial logs of the committed-source `_wklast/desktop.elf`. A from-scratch
rebuild per the task recipe (into `build/os/_wkovmf/`) was blocked by an unrelated,
in-flight parallel-lane compile break in `src/lib/gc_async_mut/gpu/engine2d/engine.spl`
(`cannot infer field type ... Engine2D field 'software_backend'`, method
`draw_software_offscreen_opacity_consume`) — downstream renderer code, out of this
lane's scope.

### Recommendation

Reclassify: the OVMF pre-spl_start stall/fault is RESOLVED / not reproducible.
Open a separate bug for the shared first-frame heap exhaustion
(`rt_array_repeat` in `render_baremetal_first_frame`, 192MB heap), which is what
now prevents `desktop-ready` under both boot modes.
