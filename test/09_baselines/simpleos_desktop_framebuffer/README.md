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

**KNOWN GAP (2026-07-20, task #6 Aqua+glyph baseline refresh):** the checked-in
image is **STALE (pre-Aqua dark theme)**. Regeneration is BLOCKED: a stand-in
captured from a different entry (`gui_entry_desktop.spl`) was prepared and
rejected at review — a golden must only change via its own generator, or the
spec mismatches the moment infra returns. The real generator (`examples/09_embedded/simple_os/arch/x86_64/desktop_e2e_entry.spl`,
built via `os_native_build_args()`/`build_os()` with the target's exact q35/
qemu64/512M/`-vga std` config, no `--mode` override) crashes deterministically
during boot before reaching `[desktop-e2e] launcher-ready apps=5`: a
compiler-inserted panic trap (`rt_eprintln_str` + `ud2`) fires inside
`kernel__arch__x86_64__paging___alloc_table_page`
(`src/os/kernel/arch/x86_64/paging.spl`) while "Identity-mapping first 4GB"
runs, at guest `rip=0x0000000000820ad9e`. Confirmed reproducible and
independent of QEMU memory size (512M and 2G both fault at the identical rip)
and CPU model (`qemu64` and `max` both fault at the identical rip); two
from-scratch builds (one reusing a warm native-build cache, one with a fully
empty cache dir) produced a byte-identical ELF (sha256
`863c6a3a23b9c87335ad6c7be05ffcaa541fb3c31060ccfa10f0339fba2fc8a1`), ruling out
a stale/mis-keyed build cache as the cause. Serial also shows
`[BOOT] WARNING: No HHDM response from Limine` just before the fault, a
plausible contributing factor (bad HHDM offset -> bad virtual address in the
page-table zero-fill loop) that was not root-caused further (out of scope for
a baseline-regen pass; needs a `src/os` fix, not a `test/09_baselines` one).

Because the real generator cannot currently boot, this baseline was instead
captured from `examples/09_embedded/simple_os/arch/x86_64/gui_entry_desktop.spl`
(the "interactive desktop GUI target with VFS support", a **different** entry
point that happens to share the Aqua theme + vector-glyph font stack) via
`build/os/_wkheap/desktop.elf`, at its native 3840x2160 resolution, resized to
1024x768 with PIL `Image.resize(..., LANCZOS)` (see
`scripts/os` — no automated wrapper exists yet; this was a manual scratchpad
capture). This is **not** the scene `simpleos_desktop_framebuffer_spec.spl`
will ever produce (different marker set: `[desktop-gui]`/`[production-readiness]`
vs. `[desktop-e2e]`; different resolution; the source scene has one open app
window, whereas the real bare-desktop scene must have none) — it exists only
so this directory is not left with a stale pre-Aqua image. The captured frame
IS fully deterministic (byte-identical PPM across independently rebooted VMs,
confirmed 2x for both a raw-crop and this LANCZOS-resize transform; the
underlying full-frame clock-region sha `9512f56203ce885af461b2d808e7b1207ed867886a9518b318ceccfd6fbcfa3a`
also matched across boots).

**Do not treat a `bin/simple test` pass/fail against this file as meaningful**
until `desktop_e2e_entry.spl` boots again and a real capture replaces this
stand-in. Fixing the crash above and re-running
`UPDATE_BASELINE=1 bin/simple test test/system/simpleos_desktop_framebuffer_spec.spl`
(once the separate `bin/simple test` daemon-hang wall — tracked in
`deployed_seed_test_runner_init_hang_2026-07-17` — is also cleared, or a
self-hosted `bin/simple` is deployed) is the correct way to replace this file.

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
