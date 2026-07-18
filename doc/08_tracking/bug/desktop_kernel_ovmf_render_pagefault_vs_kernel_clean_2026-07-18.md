# Desktop renders 99.83% under -kernel but page-faults to black (0%) under OVMF real firmware

**Date:** 2026-07-18
**Status:** OPEN — isolated to NVMe storage init (the RENDER is board-runnable, proven below). Fix scoped.
**Severity:** high (blocks board evidence WITH NVMe attached; real hardware has NVMe)

## CONFIRMED 2026-07-18: the render IS board-runnable; NVMe init is the sole blocker

Booting the SAME `desktop.elf` under OVMF pflash **with the NVMe device detached** renders
**99.83% non-black** (nonblack=8280330/8294400, 13 colors), reaching `first-frame-rendered` +
`desktop-ready`, with only 2 stray fault lines (vs a 7.4MB `[fault]` cascade when NVMe is attached).
So under REAL FIRMWARE the desktop render is identical to `-kernel` — the render is board-runnable.
The ONLY thing that breaks OVMF-with-NVMe is `_nvme_init_controller` faulting on the OVMF-relocated
high-half BAR. Fix that one guard and OVMF-with-NVMe renders too. (Repro: `scratchpad/boot_ovmf_nonvme.sh`.)

## Symptom

The x86_64 glass desktop (`examples/09_embedded/simple_os/arch/x86_64/gui_entry_desktop.spl`)
renders a full frame under QEMU `-kernel` boot — QMP screendump **99.83% non-black**
(nonblack=8280330/8294400, 13 colors), reaching `first-frame-rendered` +
`desktop-ready` + live event loop with 0 heap allocations.

The SAME `desktop.elf`, booted under **real firmware** (OVMF pflash → grub-mkstandalone
BOOTX64.EFI → multiboot), boots correctly through the firmware ladder
(`BdsDxe` → `[grub-uefi] multiboot loading` → `[BOOT64] entry/idt/call _start` →
`[desktop-gui] spl_start`) and detects the framebuffer, but then **page-faults during
render** and never paints: QMP screendump **0.00% non-black (2 px, black screen)**.

## Evidence (2026-07-18)

- `-kernel`: COVERAGE 3840x2160 nonblack=8280330/8294400 (99.83%) colors=13; scanout BAR = 0xFD000000.
- OVMF pflash: COVERAGE 3840x2160 nonblack=2/8294400 (0.00%) colors=2; scanout BAR = 0x80000000
  (OVMF's PCI enumeration relocates the std-vga BAR — `[scanout-evidence] address=2147483648`).
- Under OVMF the kernel reaches `[wm-frame] host-gpu-fallback ... width=3840 height=2160`, then
  the first `[fault] *** EXCEPTION FRAME ***` appears (serial line ~97) and cascades (7.4MB serial;
  crt0's recover-and-continue stub advances RIP by 2 and re-faults). NO `first-frame-rendered`.
- First fault frame: `rip=0x000000000800a1bb errcode=0 cs=0x08 cr2=0xffffc00000004000 cr3=0x18004000`.
  A second frame shows `cr2=0xffffffffffffff8c` (near-null/garbage). RIP is in the kernel code region
  (~0x0800_0000 / 128MB base), not the framebuffer.

## Why this was newly exposed

Before the first-frame heap fix (software_backend wiring, 77acb3e4b8b), BOTH boot modes died at the
same `[PANIC] heap exhausted` inside render_baremetal_first_frame, so the OVMF render path never ran
far enough to hit this. With the heap panic gone, `-kernel` renders cleanly but OVMF now hits a
DIFFERENT, real fault — a page fault during render under OVMF's memory layout. The earlier
`desktop_kernel_ovmf_grub_boot_stall_pre_spl_start_2026-07-18.md` (RESOLVED) covered the PRE-spl_start
stall; this is a distinct POST-spl_start render-time fault.

## Root cause (RIP decoded — it is NOT the render path)

`nm build/os/_wkheap/desktop.elf` places the faulting RIP `0x0800a1bb` inside
**`_nvme_init_controller`** (nearest symbol `08009f30 _nvme_init_controller`, ~0x28b in). So the
fault is in **NVMe controller init**, not the framebuffer/render path. The desktop RENDER is fine
(it produces 99.83% under `-kernel`); what differs under OVMF is storage bring-up:

- Under OVMF, PCI enumeration relocates the NVMe BAR to a high MMIO address (cr2 shows
  `0xffffc00000004000`, a high-half canonical address; a second frame shows `0xffffffffffffff8c`).
  `_nvme_init_controller` dereferences that BAR, but the kernel's page tables (cr3=0x18004000) do
  not map it → page fault. crt0's recover-and-continue stub advances RIP by 2 and re-faults,
  cascading (7.4MB serial) and corrupting enough state that the subsequent render never displays →
  black screen.
- Under `-kernel`, the same NVMe path SOFT-FAILS gracefully (`[vfs-init] NVMe + FAT32 unavailable`)
  rather than hard-faulting — the BAR is at an address that either maps or short-circuits before the
  faulting dereference. So `-kernel` limps past NVMe and renders.

This is the same class as the known `NVMe BAR PML4[1] user-AS gap` note: a BAR mapped in a PML4 slot
the active page tables don't cover. NVMe/disk is NOT required for the desktop render (the `-kernel`
99.83% frame renders with vfs unavailable), so the fix does not need working NVMe — it needs
`_nvme_init_controller` to SOFT-FAIL on an unmapped/high BAR under OVMF instead of dereferencing it
and faulting.

## Fix direction

- Guard the BAR access in `_nvme_init_controller`: if the NVMe BAR is unmapped / above the mapped
  window (or map it before use), soft-fail to "NVMe unavailable" the way the `-kernel` path already
  does, instead of dereferencing and page-faulting. Then the render (already working) proceeds under
  OVMF. OR map the OVMF-relocated NVMe BAR into the kernel page tables before init.
- Lower-priority alternative for a pure render-evidence screendump: boot OVMF WITHOUT the NVMe device
  attached (the desktop renders without disk) — but the real fix is the BAR guard so board hardware
  with real NVMe still boots.

## Repro

Build `build/os/_wkheap/desktop.elf` (current source), then:
- `-kernel`: `scratchpad/boot_diag_wkheap.sh` → 99.83%.
- OVMF: `scratchpad/boot_ovmf_wkheap.sh` (grub-mkstandalone BOOTX64.EFI + pflash CODE/VARS + ESP
  bootindex=0 + NVMe font disk + std-vga + QMP screendump) → 0.00% + `[fault]` cascade.

## Next steps

- Decode which mapping RIP 0x0800a1bb touches (map against the desktop.elf symbol table:
  `addr2line`/`nm` on 0x0800a1bb) — identify whether it is the framebuffer blit, a page-table walk,
  or a render-buffer access.
- Compare the page-table / framebuffer-mapping setup between the two boot modes at the point of the
  full-surface paint (not just the probe). Likely fix: map the framebuffer (and any render scratch)
  for the OVMF-relocated BAR / high-half address before the first full paint.
- Board-runnable rule: this MUST be fixed (or explicitly scoped out by the user) before the desktop
  render can be called board-runnable. The `-kernel` 99.83% screendump is real but is NOT board-runnable
  evidence on its own.

## CORRECTION 2026-07-18 (NVME-OVMF investigation lane) — the fault is in C, not the Simple driver

An investigation lane re-decoded the faulting RIP and corrected the attribution above:

- `_nvme_init_controller` (RIP 0x0800a1bb) is a **`static` C function in
  `examples/09_embedded/simple_os/arch/x86_64/boot/baremetal_stubs.c:1606`**, NOT the pure-Simple
  `src/os/drivers/nvme/` driver. The earlier "guard the Simple driver" direction is therefore WRONG.
- The pure-Simple path (`NvmeDriver.init_from_grant`, `_NvmeDriver/driver_operations.spl`) runs
  FIRST, maps BAR0, reads CAP **without faulting**, and cleanly soft-fails
  (`"nvme-missing-nvm-command-set"`). The page fault comes ~50 lines LATER from a SECOND, independent
  NVMe init inside the C bridge: `[nvme-c] BAR0=0xffffc00000004000` → immediate page fault (cr2 matches).
- Plausible (NOT pinned) entry mechanism: a **syscall-number collision** — C dispatcher case 85 =
  `NvmeReadSector` (`baremetal_stubs.c:5502`), but Simple's `os/userlib/device.spl` uses syscall 85 =
  `FreeDma`/`FreeDmaForDevice`. There is NO canonical syscall-number registry (grep confirms). A
  `free_dma_for_device(virt, size, owner_device)` with nonzero owner would land in C as
  `_nvme_read_sector(a0,a1,a2)`, pass the `buf!=0` check, and trigger the lazy `_nvme_init_controller()`.

### Corrected fix direction (NOT pure-Simple)

The fix lives in C/asm, not `.spl`:
1. Guard the C `_nvme_init_controller` (baremetal_stubs.c) to check the BAR is mapped / low before
   dereferencing, and soft-fail otherwise (NVMe not needed for render); OR
2. Map the OVMF-relocated high-half NVMe BAR into the kernel page tables (crt0.s / page-table setup)
   before that init; OR
3. Resolve the syscall-85 `NvmeReadSector`-vs-`FreeDma` collision (needs BOTH the Simple call sites
   AND the C dispatcher to agree on a non-colliding number) — establish a canonical syscall registry.

A pure-`.spl` guard in the Simple NVMe driver (attempted) is INERT — it soft-fails a path that already
soft-fails; it does not touch the C second-init that actually faults.
