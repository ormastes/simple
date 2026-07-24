# SimpleOS WM Fresh Stage-3 Kernel Stops in UEFI Before `_start`

## Status

Resolved on 2026-07-24 in
`scripts/check/check-simpleos-wm-fullscreen-evidence.shs`.

The fullscreen wrapper omitted the OVMF video modules already used by the
canonical readiness/evidence launchers. Embedding `efi_gop`, `all_video`,
`efi_uga`, `gfxterm`, `video_bochs`, and `video_fb`, then setting
`gfxpayload=text`, made the same fresh Stage-3 kernel reach `[desktop-gui]`,
initialize the compositor, and publish the 3840x2160 scanout marker.

Pixel verification is now blocked later by the separate freestanding
`ByteSpan.starts_with` CSS scanner fault recorded in
`simpleos_wm_freestanding_bytespan_css_scan_fault_2026-07-24.md`.

## Symptom

The canonical OVMF/GRUB wrapper loads
`/boot/kernel.elf`, reports no suitable video mode, and then raises an x86
general-protection exception at `RIP=FFF1000000000000`. Neither `[BOOT32]` nor
`[BOOT64]` is printed, so SimpleOS and the Web renderer never execute.

Two launches of the same freshly built kernel produced the same pre-kernel
failure and ended as:

```text
simpleos_wm_fullscreen_status=fail
simpleos_wm_fullscreen_reason=dynamic-scanout-or-desktop-readiness-missing
```

## Provenance

- Wrapper: `scripts/check/check-simpleos-wm-fullscreen-evidence.shs`
- Build directory:
  `build/wm_glass_theme_qemu_fallback_2026-07-24`
- Report:
  `doc/09_report/wm_glass_theme_qemu_fallback_2026-07-24.md`
- Serial:
  `build/wm_glass_theme_qemu_fallback_2026-07-24/serial.log`
- Pure-Simple Stage-3 compiler SHA-256:
  `6175ea1aa13576afe699a35a6521ed5defa258caefe0b4ca7da50a2cf813b62b`
- Kernel SHA-256:
  `c23c491776f1443aee04f1b92f7206190c083e93932df4987bcc9fcf84ad6e7e`
- Kernel format: ELF32 i386, entry `0x0800001c`

The immediately preceding run used an older Stage-3 compiler
(`80136ad...`), entered SimpleOS, and faulted later in `sfnt.find_table`; it is
not renderer evidence. The current compiler removes that old miscompile but
exposes the deterministic UEFI handoff failure above.

## Expected

OVMF and GRUB reach `[BOOT32]`, `[BOOT64]`, and `[desktop-gui] spl_start`, then
the canonical wrapper captures independent QMP framebuffer evidence.

## Resolution evidence

- First post-fix run:
  `doc/09_report/wm_glass_theme_qemu_video_fix_2026-07-24.md`
- Final bounded run:
  `doc/09_report/wm_glass_theme_qemu_span_fix_2026-07-24.md`
- Fresh kernel SHA-256:
  `7886122398b3931c9f75968f38377819bd8930500930ee5c2a58ecf05931eebb`
- Observed scanout:
  address `0x80000000`, 3840x2160, stride 15360, ARGB8888

## Historical resume command

Investigate the fresh ELF/GRUB handoff before rerunning theme pixels. Compare
the current kernel's multiboot header, load segments, relocation/layout, and
GRUB handoff against the retained July 20 passing kernel:

`build/wm_glass_theme_qemu_postfix_2026-07-20/simpleos_wm_production_desktop.elf`

After fixing the handoff, rerun exactly:

```sh
BUILD_DIR=build/wm_glass_theme_qemu_fallback_2026-07-24 \
REPORT_PATH=doc/09_report/wm_glass_theme_qemu_fallback_2026-07-24.md \
SIMPLE_BIN=build/bootstrap/stage3/aarch64-apple-darwin/simple \
SIMPLE_BIN_SOURCE=explicit-fresh-pure-simple-stage3 \
sh scripts/check/check-simpleos-wm-fullscreen-evidence.shs
```

Do not reuse the July 20 framebuffer as proof for the current renderer source.
