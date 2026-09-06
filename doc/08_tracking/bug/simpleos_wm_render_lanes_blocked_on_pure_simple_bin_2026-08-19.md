# SimpleOS WM rendering evidence lanes blocked: no usable pure-Simple build binary

- **Date:** 2026-08-19
- **Status:** BLOCKED (dependency), not a lane defect
- **Lanes affected:**
  - `scripts/check/check-simpleos-x86-64-wm-render-event-evidence.shs` (execs the canonical wrapper)
  - `scripts/check/check-simpleos-wm-fullscreen-evidence.shs` (canonical)
  - `scripts/check/check-simpleos-wm-aqua-glyph-ovmf-evidence.shs` (needs `SIMPLEOS_KERNEL_ELF` built out-of-band — same builder dependency)

## Evidence (2026-08-19, worktree /mnt/data/worktrees/render-harden)

Run log: session scratchpad `wm_fullscreen.log`. Verdict lines:

```
simpleos_wm_fullscreen_status=fail
simpleos_wm_fullscreen_reason=simple-bin-forbidden
simpleos_wm_fullscreen_simple_bin_source=auto-cached-pure-simple-provenance-forbidden
simpleos_wm_fullscreen_simple_bin_resolved=/mnt/data/worktrees/simple-main/bin/release/x86_64-unknown-linux-gnu/simple
simpleos_wm_fullscreen_simple_bin_sha256=557757bf6882abb36735857599dc29c5eb96252ab064f2ad4f5c1bf9af8b8ea7
```

The wrapper auto-discovers a build binary and enforces pure-Simple provenance for
the kernel build (`gui_entry_desktop.spl` native-build). The only deployed
candidate (`bin/release/x86_64-unknown-linux-gnu/simple`) self-identifies as the
Rust bootstrap seed, so the lane correctly refuses it (exit 0 with
`status=fail`, `reason=simple-bin-forbidden` — a refusal, not a crash).

Aqua-glyph lane run (`wm_aqua_glyph_ovmf.log`):
`wm_aqua_glyph_ovmf_evidence: not-ready`, `reason: SIMPLEOS_KERNEL_ELF is not set`
— same root cause: no coordinator build step can produce the desktop kernel ELF
without an admitted pure-Simple builder.

## Root cause / dependency

All four git-tracked stage binaries SEGV on `compile` and `native-build`
(`doc/08_tracking/bug/stage3_native_build_and_compile_segv_on_hello_world_2026-08-18.md`,
`check-stage-binaries-runnable.shs` FAIL 2026-08-18). Until a working
self-hosted `bin/simple` is deployed, no provenance-admissible builder exists
for the desktop WM kernel, so no in-guest desktop/browser-engine render
evidence can be produced on x86_64 or aarch64.

## Not blocked (verified same day)

- `check-simpleos-qemu-engine2d-simd-kernels.shs`: PASS (static symbol/receipt check, no QEMU boot).
- `check-simpleos-baremetal-engine2d-spans.shs`: PASS after fixing the
  overlapping-span blend defect in `baremetal_stubs.c` (separate fix, this session).

## Additional same-day evidence

- `check-simpleos-x86-64-wm-qemu-readiness.shs` with
  `SIMPLEOS_KERNEL_ELF=build/os/simpleos_wm_input_test_x86_64.elf`: real
  OVMF pflash + GRUB EFI boot succeeded (`grub_efi_ran=true`,
  `kernel_start_reached=true`); in-guest serial shows
  `[wm-input-test] framebuffer marker OK`, `[PASS] wm_input_test_entry`,
  `TEST PASSED`. Verdict is `not-ready` only because the DESKTOP kernel's
  `[desktop-gui] spl_start` marker is absent — the desktop kernel cannot be
  built (this bug). QEMU + firmware chain and in-guest framebuffer rendering
  are proven healthy.
- `check-simpleos-arm64-efi-real-firmware-boot.shs`: `ERROR — nothing was
  checked: ESP build failed ... missing kernel ELF
  build/os/aarch64_limine/kernel.elf` — same builder dependency
  (`build/os/arm64_wm_ramfb_screendump.blocker.txt`:
  `arm64-wm-target-did-not-build`).

## Unblock path

Deploy a working pure-Simple `bin/simple` (bootstrap redeploy tracked in the
stage-binary SEGV bug), then re-run the fullscreen lane; it builds the kernel
itself and the aqua-glyph lane can consume the same ELF.
