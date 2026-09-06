# No installed CLI/demo binary can drive lavapipe to a raw pixel dump without new host code

Status: OPEN (P3)
Status re-verified 2026-08-17 by source inspection (triage shard 00).

**Date:** 2026-08-11
**Lane:** L3, board Vulkan readback boundary (`vulkan.present.readback_image@1`)
**Architecture:** doc/04_architecture/os/vulkan/simpleos_board_vulkan_driver_architecture_2026-08-10.md
**Related:** src/os/drivers/gpu/board_vulkan/boundary_readback_gate.spl, boundary_readback_lavapipe_provider.spl

## Finding

Investigated whether the lavapipe reference side of the readback boundary
comparison could be upgraded from caller-supplied image bytes to a genuinely
**executed** counterpart, driven purely via subprocess (`process_run_bounded`)
with no new native (C/C++) tooling, per the `.spl`-only scope of this lane.

Host has:
- `vulkaninfo` (`/usr/bin/vulkaninfo`) — reports instance/device info and
  supported extensions/formats only. No rendering, no pixel output, `-o`
  writes the *info report* to a file, not an image.
- `vkcube` / `vkcube-wayland` (`/usr/bin/vkcube*`, from `vulkan-tools`
  1.3.275.0+dfsg1-1) — renders a spinning cube, but **requires a live
  `DISPLAY`/Wayland surface** (`Environment variable DISPLAY requires a valid
  value. Exiting ...` when run headless) and has no flag to dump frames to a
  file (checked `vkcube --help`: `--use_staging --validate
  --validate-checks-disabled --break --c <framecount> --suppress_popups
  --incremental_present --display_timing --gpu_number --present_mode --width
  --height --force_errors` — no screenshot/dump/output-file option anywhere in
  that list).
- No `glmark2`, `vkmark`, `deqp`/Vulkan-CTS, or any other Vulkan sample binary
  is installed.

`VK_EXT_headless_surface` is advertised by the loader/lavapipe instance, so a
purpose-built harness *could* render off-screen and dump raw pixels — but
using it requires writing new Vulkan host code (a minimal C or Rust program
calling `vkCreateHeadlessSurfaceEXT`, blitting the render target to a linear
buffer, and writing raw bytes/PPM). That is explicitly out of scope for this
lane (".spl-only", "no new host packages, no writing a C Vulkan program from
scratch").

## Conclusion

There is genuinely no way, on this host, to get real lavapipe pixels via
subprocess alone within pure Simple/.spl scope. `boundary_readback_gate.spl`
therefore keeps the counterpart image as caller-supplied bytes (documented as
such, never claimed as an executed capture), and
`board_vulkan_readback_attempt_status` continues to report `unavailable` for
the candidate side — which is correct regardless of this gap, since SimpleOS
cannot render at this boundary today either.

## What would close this

Either:
1. A new minimal Vulkan headless capture binary (native code, new artifact,
   explicitly out of this lane's `.spl`-only scope), invoked via
   `process_run_bounded` with `VK_ICD_FILENAMES=/usr/share/vulkan/icd.d/lvp_icd.json`,
   dumping a raw/PPM framebuffer for a fixed scene; or
2. Installing a Vulkan sample tool that already supports headless pixel dump
   (e.g. some `vulkan-samples` or `Sascha Willems` demo builds do, but none is
   currently installed and adding one is a host-package change outside this
   lane's boundary).

No tolerance was introduced and no execution was fabricated to work around
this gap.
