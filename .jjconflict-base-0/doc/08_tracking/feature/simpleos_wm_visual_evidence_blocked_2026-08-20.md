# SimpleOS WM Visual Evidence — Live Acceptance Blocker

Date: 2026-08-20

## Status

`BLOCKED[REQ-017-LIVE-GUEST]`

Production-owner host fixtures now cover focus/z-order, focused-close fallback,
bounded damage, focused input routing, composited overlap pixels, and restart
fencing in
`test/03_system/os/wm/simpleos_wm_behavior_evidence_spec.spl`. They are not
SimpleOS guest or physical-display evidence.

## Missing evidence

- admitted pure-Simple SSpec runtime and current SimpleOS WM image;
- successful canonical QEMU/OVMF boot and QMP capture;
- one evidence record binding pointer input sequence, scene/content mutation,
  presentation generation, framebuffer readback, and QMP pixels;
- nonempty hash-addressed baseline, fullscreen, restored, and browser-event
  frames with fullscreen different from baseline and restore equal to baseline;
- AArch64, RV64GC, native-host, and physical-board rows required by the umbrella
  matrix.

No source scan, host fixture, screenshot existence check, fabricated handle,
zero frame, or prior report may close this blocker.

## Resume contract

Run the executable spec once through an admitted pure-Simple runtime. Its live
scenario owns this exact wrapper invocation and artifact directory:

`BUILD_DIR=build/test-simpleos-wm-hardening-behavior REPORT_PATH=build/test-simpleos-wm-hardening-behavior/report.md /bin/sh scripts/check/check-simpleos-wm-fullscreen-evidence.shs`

On a nonzero wrapper exit or missing/corrupt artifact, preserve
`BLOCKED[REQ-017-LIVE-GUEST]` with the exit identity. Never convert unavailable
hardware/runtime to PASS or skip. After x86_64 closes, run the architecture and
physical rows independently; do not infer them from the x86_64 QEMU bundle.
