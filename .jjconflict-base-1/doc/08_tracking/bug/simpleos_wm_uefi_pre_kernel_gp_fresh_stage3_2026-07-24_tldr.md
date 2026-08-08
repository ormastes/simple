# SimpleOS WM UEFI Pre-Kernel GP — TLDR

- Status: resolved on 2026-07-24.
- Cause: fullscreen wrapper omitted OVMF GOP/video modules.
- Fix: embed `efi_gop`, `all_video`, `efi_uga`, `gfxterm`,
  `video_bochs`, and `video_fb`; set `gfxpayload=text`.
- Proven: fresh Stage-3 kernel reaches desktop compositor and 3840x2160
  scanout.
- Remaining pixel blocker is separate:
  `simpleos_wm_freestanding_bytespan_css_scan_fault_2026-07-24.md`.
