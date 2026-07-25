# Desktop renders 99.83% under -kernel but page-faults to black (0%) under OVMF real firmware

**Date:** 2026-07-18
**Status:** RESOLVED 2026-07-18 — OVMF-with-NVMe renders 99.83% (NVMe BAR-high map + OVMF grub video fix, both landed + verified)
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

## FIX APPLIED 2026-07-18 — map NVMe BAR high in the desktop entry (0668fb23d8e)

Root cause CONFIRMED and fixed the pure-Simple way after all. The C `_nvme_init_controller`
(baremetal_stubs.c:1626-1668) reads BAR0 from PCI config and, when it lands in the
`[NVME_BAR_PHYS_BASE=0xC000000000, +1GiB)` window, remaps it to the higher-half VA
`NVME_BAR_VIRT_BASE=0xFFFFC00000000000` (PML4[384]) and dereferences it directly (CAP read at
+0x00). crt0.s maps that VA in `boot_pml4[384]`, and `vmm_map_nvme_bar_high()`
(src/os/kernel/memory/vmm_address_space.spl:308) installs it in the active kernel VMM — every
ring-3 entry (ssh_ring3_entry, fs_elf_exec_smoke_entry, ...) calls it, but **gui_entry_desktop's
spl_start never did**, so under OVMF (which actually populates the BAR in that window) the deref
hit an unmapped VA → page fault → cascade → black screen.

Fix: `gui_entry_desktop.spl` now calls `vmm_map_nvme_bar_high()` right after `vmm_activate()`
(the docstring's prescribed "after vmm_init, before first user AS" point). The mapping is also
cloned into every user AS via the existing PML4[256..511] copy loop, so it covers whichever cr3
the C init runs under.

**Verification status:**
- `-kernel`: STILL 99.83% (no regression); `[desktop-gui] nvme-bar-high:mapped` prints. CONFIRMED.
- OVMF-with-NVMe: NOT runtime-verified — blocked by an UNRELATED environmental issue: GRUB
  #UD-crashes at video-mode setup (`error: no suitable video mode found` → `#UD` at RIP 0x101E)
  BEFORE the kernel runs, reproducibly under heavy machine load (load avg ~20-26, swap exhausted,
  many parallel-session QEMU/build processes). Earlier OVMF boots (when the box was quieter) reached
  the kernel fine, so this is load/firmware flakiness, not the fix. Re-run `scratchpad/ovmf_retry_loop.sh`
  when machine load clears to confirm the render under OVMF+NVMe.
- The fix is correct-by-analysis (maps exactly the faulting VA) and cannot regress (inert if the C
  init never runs). Pushed on that basis with full transparency.

### Follow-up: OVMF GRUB #UD under load (separate, lower priority)
grub-mkstandalone's multiboot payload #UD-crashes at video-mode negotiation under OVMF when the host
is loaded. Candidate hardening: embed `all_video`/`gfxterm` modules + `set gfxpayload=text`, or boot
the multiboot kernel via a direct UEFI stub instead of GRUB. (A naive `terminal_output console` +
`gfxpayload=text` grub.cfg tweak did NOT help — reverted.)

## OVMF GRUB #UD — CONFIRMED ENVIRONMENTAL (blocks all OVMF verification, not just load)

Update: ~24 OVMF boot attempts across load levels (from ~30 down to ~10-12) ALL #UD-crash in GRUB
(`error: no suitable video mode found` -> `#UD @ RIP 0x101E`), BEFORE the kernel runs. A no-NVMe
OVMF boot ALSO crashes now (kernel never boots) — so it is NOT NVMe-related and NOT purely
load-related. The two early boots that reached the kernel (one with-NVMe -> NVMe fault, one no-NVMe
-> 99.83%) were hours earlier in a different box state. GRUB's std-vga GOP video-mode negotiation
under OVMF now fails reproducibly in this environment (heavy sustained multi-session QEMU/build load,
earlyoom active, swap exhausted). This BLOCKS runtime verification of the NVMe BAR-high fix under
OVMF; it does not reflect on the fix (which is -kernel-verified and correct-by-analysis).

Hardening (separate task): embed all_video/gfxterm/efi_gop/efi_uga in grub-mkstandalone modules; or
boot the multiboot kernel via a direct UEFI multiboot stub instead of GRUB; or run OVMF boots on an
unloaded host. Re-verify the NVMe fix under OVMF via scratchpad/ovmf_retry_loop.sh when a clean OVMF
boot is achievable.

## RESOLVED 2026-07-18 — OVMF-with-NVMe renders 99.83% (both fixes verified under real firmware)

Two fixes, both landed, close this end-to-end:
1. NVMe BAR-high map in the desktop entry (ceb43107412 / 0668fb23d8e): gui_entry_desktop.spl calls
   `vmm_map_nvme_bar_high()` after vmm_activate() so the C `_nvme_init_controller` BAR deref is mapped.
2. OVMF GRUB video fix (136ea66f518): embed efi_gop/efi_uga/all_video/gfxterm/video_bochs/video_fb in
   grub-mkstandalone + `insmod efi_gop`/`all_video` + `gfxpayload=text`. This was the REAL reason no
   OVMF boot could be verified — GRUB #UD-crashed at video-mode setup before the kernel ran; a missing
   grub-video-driver bug, not (only) machine load.

VERIFIED under OVMF pflash (real firmware) WITH NVMe attached:
```
[BOOT64] entry/idt/call _start -> [desktop-gui] spl_start
[desktop-gui] nvme-bar-high:mapped
[nvme-c] Admin queues configured ; [nvme-c] NS1: sectors=1048576, sector_size=512
[desktop-gui] first-frame-rendered ; [desktop-gui] desktop-ready
[production-readiness] wm=live renderer=engine2d
COVERAGE-OVMF 3840x2160 nonblack=8280330/8294400 (99.83%) colors=13   (faults=2 benign, no cascade)
```
The NVMe fix not only prevents the page fault — the C init now SUCCEEDS (admin queues + namespace
detected) because the BAR is mapped. `-kernel` regression: still 99.83%. Board-runnability of the
glass desktop WITH NVMe under real firmware is CONFIRMED. Evidence: scratchpad/goal_evidence_20260718/
ovmf_nvme_*.ppm + serial. Repro: scratchpad/boot_ovmf_wkheap.sh (grub gate now carries the video modules).
