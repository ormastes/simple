# `detect_virtio_gpu_device` is a plain existence check, not a device-type probe — misroutes `unavailable_reason()` on any existing non-device file

**Status:** Resolved
**Filed:** 2026-08-07
**Resolved:** 2026-08-07
**Component:** `src/os/compositor/vulkan_compositor_backend.spl`
**Found by:** V1 unit (`doc/03_plan/ui/testing/render_2d_vulkan_functional_coverage_plan_2026-08-07.md`)

## Summary

`detect_virtio_gpu_device` (`src/os/compositor/vulkan_compositor_backend.spl:42-49`)
is documented and implemented as a bare `file_exists(render_node)` call — it
returns `true` for *any* path that exists on disk, not only a real DRM render
node (e.g. `/dev/dri/renderD128`). The plan that commissioned this file's
test-closure unit (`render_2d_vulkan_functional_coverage_plan_2026-08-07.md`,
unit V1, line 461) states the expected behavior as "a plain file → false",
i.e. it expected some minimal device-type discrimination. The shipped
function does not do this; its own docstring already says so honestly:

```
src/os/compositor/vulkan_compositor_backend.spl:42
pub fn detect_virtio_gpu_device(render_node: text) -> bool:
    """REAL, VERIFIABLE capability probe: does a DRM render node exist at
    this path on disk? ... It does NOT mean virtio-gpu specifically (any DRM
    render node passes) ..."""
    file_exists(render_node)
```

## Why this matters (not cosmetic)

`VulkanCompositorBackend.create_with_render_node` stores the probe result as
`device_node_present` (`vulkan_compositor_backend.spl:79`), and
`unavailable_reason()` branches on exactly that flag
(`vulkan_compositor_backend.spl:91-97`):

- `device_node_present == false` → `"no_drm_render_node:{path}:qemu_only"`
- `device_node_present == true`  → `"vulkan_venus_session_not_implemented:qemu_only:board_gap_open"`

So pointing the constructor at any existing plain file (e.g. `/etc/hostname`)
makes the backend report the wrong reason: it claims a DRM node was found and
only the venus session is missing, when in truth no DRM/GPU device was ever
checked. This is a fail-open misreport of *which* honesty-gate branch is
active — the same class of defect the file's own header explicitly warns
against ("Flipping it without that work landing is exactly the 'looks wired
but isn't' failure mode this lane was told to avoid").

## Current test posture

`test/01_unit/os/compositor/vulkan_compositor_backend_spec.spl` — describe
block `"detect_virtio_gpu_device is a plain filesystem existence probe (KNOWN
LIMITATION, tracked)"` — pins the REAL, documented behavior (`true` for
`/etc/hostname`) rather than asserting a stricter check the code does not
implement (which would just be a fabricated expectation, not a fix). It does
not silently accept the risk: the describe-block docstring and this bug doc
both record the misrouting consequence.

## Unblock condition

Either:
1. Add a minimal real device-type check (e.g. `stat` mode bits for a
   character device, or match against a `/dev/dri/render*` name pattern)
   so `detect_virtio_gpu_device` only returns `true` for something
   plausibly DRM-shaped, matching the plan's literal expectation; or
2. If a stricter check is judged not worth building before venus/Vulkan
   support itself lands (this whole file is a rejecting no-op skeleton), a
   maintainer records that decision explicit here and downgrades the plan's
   V1 acceptance line to match documented reality — do not leave the
   contradiction between the plan text and the shipped function's docstring
   unresolved.

Not scheduled as part of V1 (V1 is spec-closure only, source only gets the
minimal trait-conformance `report_damage` addition it needed to compile).

## Resolution (2026-08-07)

Took unblock option 1: `detect_virtio_gpu_device` (`src/os/compositor/vulkan_compositor_backend.spl`)
now checks `stat` mode bits via `shell_bool("test -c '{render_node}'")`
instead of a bare `file_exists`. `test -c` is true only for a character
device — the shape every DRM render node has — so a plain regular file or a
directory that merely exists on disk is now correctly rejected. Empty path
short-circuits to `false`. The `file_exists` import was removed (no longer
used); `shell_bool` is imported from `std.io_runtime` instead.

`test/01_unit/os/compositor/vulkan_compositor_backend_spec.spl` updated:
- The `"detect_virtio_gpu_device is a plain filesystem existence probe
  (KNOWN LIMITATION, tracked)"` describe block is replaced with
  `"detect_virtio_gpu_device requires a real device node, not just an
  existing path (fixed 2026-08-07)"`, asserting `false` for a missing path,
  an existing plain file (`/etc/hostname` — the exact case this bug
  reported), and an existing directory (`/tmp`); and `true` for a real
  character device (`/dev/null`, chosen because it is present on every
  Linux/container host this suite runs on, unlike a real DRM render node
  which is hardware-dependent and not asserted here).
- `"unavailable_reason names the unimplemented venus session and open board
  gap when the render node is present"` now points at `/dev/null` instead
  of `/etc/hostname` to reach the node-present branch, since a plain file
  no longer does.

Verified with `bin/simple test test/01_unit/os/compositor/vulkan_compositor_backend_spec.spl`:

```
Results: 21 total, 21 passed, 0 failed
```

`unavailable_reason()` no longer misroutes for an arbitrary existing
non-device file: pointing the constructor at `/etc/hostname` now correctly
reports the `no_drm_render_node` branch instead of falsely claiming a
render node was found.
