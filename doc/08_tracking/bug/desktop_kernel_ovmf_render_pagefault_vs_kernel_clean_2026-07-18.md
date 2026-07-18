
## RESOLVED 2026-07-18 — OVMF-with-NVMe renders 99.83% (both fixes verified under real firmware)

Two fixes, both landed, close this end-to-end:
1. NVMe BAR-high map in the desktop entry (ceb43107412 / 0668fb23d8e): gui_entry_desktop.spl calls
   `vmm_map_nvme_bar_high()` after vmm_activate() so the C `_nvme_init_controller` BAR deref is mapped.
2. OVMF GRUB video fix (136ea66f518): embed efi_gop/efi_uga/all_video/gfxterm/video_bochs/video_fb in
   grub-mkstandalone + `insmod efi_gop`/`all_video` + `gfxpayload=text`. This was the REAL reason no
   OVMF boot could be verified — GRUB #UD-crashed at video-mode setup before the kernel ran; it was a
   missing-grub-video-driver bug, not (only) machine load.

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
detected) because the BAR is mapped. `-kernel` regression check: still 99.83%. Board-runnability of the
glass desktop WITH NVMe under real firmware is CONFIRMED. Evidence: scratchpad/goal_evidence_20260718/
ovmf_nvme_*.ppm + serial. Repro: scratchpad/boot_ovmf_wkheap.sh (now with the grub video modules).
