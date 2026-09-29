# SimpleOS Desktop Framebuffer Baseline (SYS-GUI-006)

This directory holds the checked-in PPM baseline for
`test/system/simpleos_desktop_framebuffer_spec.spl`. The spec boots the
`x64-desktop-test` desktop target under QEMU, captures the BGA framebuffer
through QMP `screendump`, and compares the resulting PPM against
`desktop_scene.ppm`.

## Files

- `desktop_scene.ppm` - live-captured 1024x768 P6 PPM golden image for the
  bare desktop scene. This file must never be zero bytes.

## Current Status

`desktop_scene.ppm` is a real committed baseline, not a placeholder. The
current checked-in image is 1024x768 and contains non-black pixels across the
frame.

The default spec run is intentionally cheap and safe:

```
bin/simple test test/system/simpleos_desktop_framebuffer_spec.spl
```

Without `SIMPLEOS_QEMU_DESKTOP_FRAMEBUFFER_LIVE=1`, the desktop build and QEMU
capture branches are skipped. The spec still validates that the committed
baseline exists, decodes as PPM, has the expected dimensions, and is not blank.

## Live Compare

Run the live visual regression lane with:

```
SIMPLEOS_QEMU_DESKTOP_FRAMEBUFFER_LIVE=1 bin/simple test test/system/simpleos_desktop_framebuffer_spec.spl
```

This requires `qemu-system-x86_64` and a usable desktop disk image. The spec
waits for:

- `[desktop-e2e] launcher-ready apps=5`
- `[desktop-e2e] desktop-ready`

It then captures `/tmp/simpleos_desktop_capture.ppm` and compares it byte-for-
byte against `desktop_scene.ppm`. Capture failures write focused artifacts under
`build/os/simpleos_desktop_fb_spec_failure_*`.

## Updating The Baseline

Only update the golden image after intentional visual review:

```
UPDATE_BASELINE=1 bin/simple test test/system/simpleos_desktop_framebuffer_spec.spl
```

`UPDATE_BASELINE=1` automatically enables the live capture path. A successful
run rewrites `desktop_scene.ppm`; a blank capture, missing ready marker, QMP
failure, unavailable QEMU binary, or unavailable disk image must not be
committed as a replacement.

After updating, open the PPM and verify:

- the desktop background is present
- dock or taskbar chrome is present
- no panic stripes or uninitialized regions are visible
- no app windows are present in this bare-desktop baseline

Then run both checks:

```
bin/simple test test/system/simpleos_desktop_framebuffer_spec.spl
SIMPLEOS_QEMU_DESKTOP_FRAMEBUFFER_LIVE=1 bin/simple test test/system/simpleos_desktop_framebuffer_spec.spl
```

If `desktop_e2e_entry` changes resolution, update the spec's baseline
dimension assertions and refresh `desktop_scene.ppm` in the same change.
