# Production Host WM Evidence — 2026-07-24

- status: **FAIL (fail closed)**
- scope: native macOS host only; no QEMU execution was performed.
- compiler: exact-current full-bootstrap Stage3, `simple-bootstrap 1.0.0-beta`, SHA-256 `0105351a78a36ec980ac2e68795dcef60fd73e0744fd1cc6fae2fbec065bfa5d`.

## Cycle record

1. Cycle 1 used a pre-full-bootstrap Stage3. Native linking failed because its embedded native bridge did not consume the three required external providers. No hosted process was launched.
2. A full bootstrap rebuilt `libsimple_native_all.a`; the final Stage3 binary was checked for the embedded `SIMPLE_LINK_OBJECTS` capability. Cycle 2 linked `libspl_winit.dylib`, `libsimple_runtime_wm.dylib`, and `libsimple_runtime_c_wm.dylib`, then launched the real hosted executable. It printed the three startup banners and exited with `runtime error: field access on nil receiver` before `window-created` or evidence readiness.
3. Cycle 3 rebuilt and launched after the first package-boundary mitigation. It had the same exact early nil-receiver failure and generated no snapshot, capture, or input receipt. This is the final permitted host cycle; no further relaunch was attempted.

## Evidence state

- native artifact: `build/wm-host-current/evidence-cycle3/hosted_entry` (present)
- live log: `build/wm-host-current/evidence-cycle3/launch.log` (present)
- windowed/fullscreen/restored scene JSON: missing
- windowed/fullscreen/restored PPM captures: missing
- event receipts: missing

The launch log's last markers are the three `SimpleOS shared hosted WM` banners followed by `runtime error: field access on nil receiver`; it contains neither `[theme-evidence]` nor `[hosted-wm] window-created`. Therefore the defect is before native window creation, in the host theme bootstrap.

## Post-cycle source correction (not live-verified)

`host_wm_theme_bootstrap.spl` now uses the generated, manifest-stamped Aetheric snapshot that the production wrapper itself validates, rather than resolving a `ResolvedThemePackage` class on the compiled Stage3 host-startup boundary. The equivalent generated handoff is already used by freestanding SimpleOS desktop entries. The wrapper also distinguishes a child exit before evidence from an ordinary readiness timeout.

These corrections are source-reviewed and contract-pinned, but intentionally remain **unverified by a fourth live launch** to respect the three-cycle cap. No screenshot, source inspection, or demo marker is accepted as production evidence.
