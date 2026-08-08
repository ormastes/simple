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

## Security rework (2026-08-08)

A higher-model review of the 2026-08-07 resolution (commit `c2fc508a`) found
that the fix itself introduced a command-injection vulnerability. The fix
switched the probe from `file_exists` to `shell_bool("test -c
'{render_node}'")`. `shell_bool` (`src/lib/nogc_sync_mut/io_runtime.spl:88`)
executes its argument via `rt_process_run("/bin/sh", ["-c", command])`, and
`render_node` is interpolated **inside single quotes** in that command
string. Single-quoted shells strings cannot escape an embedded single
quote, so a `render_node` value containing one breaks out of the quoting.
`detect_virtio_gpu_device` is a `pub fn` — any caller (including, in
principle, untrusted config/env-derived paths) controls this argument.

Concretely, for `render_node = "'; touch /tmp/pwned; echo '"` the generated
command line was:

```sh
test -c ''; touch /tmp/pwned; echo ''
```

which (1) runs `touch /tmp/pwned` as an arbitrary injected command, and (2)
makes the final `echo` (exit code 0) the last command in the pipeline, so
`shell_bool` returns `true` regardless of whether any real device exists —
the injection doubles as a probe-result spoof. This is a command-injection
+ device-presence-spoofing defect in a `pub fn` taking arbitrary text.

### Fix

Investigated whether a no-shell stat primitive already existed
(`std.io_runtime`, `std.fs`, `io/file_ops.spl`, `rt_file_stat`): the only
stat-shaped extern, `rt_file_stat`, returns file **modification time**, not
`st_mode` bits — there is no character-device check exposed via
SFFI/`std.io_runtime`/`std.fs` today, and adding one would require new FFI
plumbing on the runtime side. Per the fix's own stated preference order,
took route (2): kept `shell_bool` (no runtime change needed) but added a
strict allowlist gate, `is_safe_render_node_path()`
(`src/os/compositor/vulkan_compositor_backend.spl`), that runs **before**
`render_node` ever reaches the shell:

- Rejects the empty string (short-circuit retained).
- Requires the path to start with `/` (absolute path only).
- Every character must be in `[A-Za-z0-9/._-]` — no quotes, semicolons,
  backticks, `$()`, backslashes, or whitespace of any kind pass.

`detect_virtio_gpu_device` now calls `is_safe_render_node_path(render_node)`
and returns `false` immediately (never calling `shell_bool`) if validation
fails. The existing `""` short-circuit is unchanged and still comes first.

### Spec updates

`test/01_unit/os/compositor/vulkan_compositor_backend_spec.spl` — added
`is_safe_render_node_path` to the import list and a new describe block,
`"security: render_node cannot break out of the shell command line (fixed
2026-08-08)"`, with 8 new examples:

- The exact injection payload from this finding
  (`'; echo pwned; echo '`) is rejected by both
  `detect_virtio_gpu_device` and `is_safe_render_node_path`.
- A `;`-separated command, a backtick command substitution, a backslash,
  and embedded whitespace are all rejected.
- A relative path (`dev/null`, `../dev/null`) is rejected.
- Legitimate absolute paths already used elsewhere in this spec
  (`/dev/null`, `/dev/dri/renderD128`, `/nonexistent/render-node-for-spec`)
  are still accepted.
- Regression guard: `detect_virtio_gpu_device("/dev/null")` still correctly
  returns `true` after the allowlist was added.

Manually confirmed no side effect from the injection payload: `/tmp/pwned`
did not exist before or after running the spec.

Verified with
`bin/simple run src/app/test_runner_new/test_runner_single.spl
test/01_unit/os/compositor/vulkan_compositor_backend_spec.spl
--no-session-daemon --sequential`:

```
Results: 29 total, 29 passed, 0 failed
```

(21 pre-existing examples plus 8 new security examples, all green; 0
regressions.)
