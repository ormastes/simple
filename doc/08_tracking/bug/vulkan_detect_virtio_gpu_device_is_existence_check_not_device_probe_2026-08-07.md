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

## Follow-up: shell-drop via a new no-shell stat primitive (2026-08-08)

The "Fix" section above investigated whether a no-shell char-device stat
primitive already existed and found none (`rt_file_stat` returns mtime, not
`st_mode`) — so the allowlist-guarded `shell_bool("test -c '{render_node}'")`
was kept as the pragmatic fix rather than adding new FFI plumbing. This
follow-up adds that plumbing and drops the shell entirely.

### New runtime primitive: `rt_file_is_char_device(path) -> bool`

Mirrors the existing `rt_file_is_regular_no_follow` in shape and wiring
(single text arg, stat(2)-backed bool), using `S_ISCHR` instead of
`S_ISREG`, and follows symlinks (`stat`, not `lstat` — the caller wants to
know whether the path ultimately resolves to a character device, not
whether the leaf entry itself is one). Wired at every site
`rt_file_is_regular_no_follow` is wired, mirroring its ABI treatment
end-to-end:

- `src/runtime/runtime.h` — declaration
- `src/runtime/runtime.c` — implementation (full runtime)
- `src/runtime/runtime_native.c` — duplicate implementation for the
  core-c-bootstrap build (native binaries linked without `runtime.c`)
- `src/compiler_rust/compiler/src/interpreter_extern/file_io.rs` —
  interpreter-path implementation (`fs::metadata` + `FileTypeExt::is_char_device`)
- `src/compiler_rust/compiler/src/interpreter_extern/mod.rs` — dispatch
  table registration (`insert_simple!`)
- `src/compiler_rust/compiler/src/codegen/runtime_sffi.rs` — `RuntimeFuncSpec`
  signature (`(ptr, len) -> bool`, single text arg)
- `src/compiler_rust/compiler/src/codegen/instr/calls.rs` and
  `src/compiler_rust/compiler/src/codegen/llvm/functions/calls.rs` —
  text-arg-index marking (`text_arg_indices`) so the codegen backends
  marshal the text argument correctly
- `src/compiler/50.mir/text_extern_abi.spl` — the pure-Simple MIR mirror
  of the same text-arg-index marking, for the self-hosted pipeline

### `.spl` wrapper: `std.io_runtime.is_char_device(path)`

`src/lib/nogc_sync_mut/io_runtime.spl` gained `extern fn rt_file_is_char_device`
and a `pub fn is_char_device(path: text) -> bool` wrapper (exported
alongside `is_dir`/`is_file`), following the file's existing wrapper
pattern.

### `detect_virtio_gpu_device` refactor

`src/os/compositor/vulkan_compositor_backend.spl`: the import changed from
`std.io_runtime.{shell_bool}` to `std.io_runtime.{is_char_device}`, and the
final line of `detect_virtio_gpu_device` changed from
`shell_bool("test -c '{render_node}'")` to `is_char_device(render_node)`.
`is_safe_render_node_path()` is unchanged and still runs first — it is now
defense-in-depth (rejecting garbage input before it reaches stat(2)) rather
than a shell-injection guard, since there is no shell left to inject into.
File-level and function-level doc comments were updated to describe the new
no-shell probe instead of the retired `test -c` shell-out.

### Spec updates

`test/01_unit/os/compositor/vulkan_compositor_backend_spec.spl` needed no
new `it` blocks: the acceptance cases this follow-up cares about
(`/dev/null` → true char device, `/etc/hostname` → false regular file, a
missing path → false, plus all 8 injection-rejection cases) were already
present from the prior fix and exercise `detect_virtio_gpu_device()`
through its public signature, so they equally cover the no-shell
implementation underneath. Two docstrings (in the "requires a real device
node" and "security" `describe` blocks) were updated to stop describing a
`/bin/sh -c "test -c ..."` shell-out that no longer exists.

### Baremetal freestanding body (SimpleOS x86_64 kernel link)

`detect_virtio_gpu_device()` is in the SimpleOS desktop-kernel's `-nostdlib`
freestanding build closure (it's reachable via the compositor-backend
selection path even though `VulkanCompositorBackend` is never actually
selected at runtime today). Once `rt_file_is_char_device` is a real extern,
the freestanding linker needs a concrete symbol for it same as every other
runtime primitive that closure pulls in — a coordinating sibling session
flagged this mid-landing (the same-day CUDA/Metal device-absent-body commit,
`0d83c56`, hit an analogous gap for 6 GPU symbols and fixed it the same
way).

Added `RuntimeValue rt_file_is_char_device(RuntimeValue path)` to
`examples/09_embedded/simple_os/arch/x86_64/boot/baremetal_stubs.c`,
directly after the CUDA/Metal device-absent block, returning `0` (false):
a baremetal kernel has no host filesystem to `stat(2)`, so "no character
device at any path" is the truthful answer, not a fabricated one — and it
is exactly the "device absent" branch `detect_virtio_gpu_device()` already
handles correctly (same as a real host with no render node present).

### Build-verify status: DEFERRED

This session could not verify the Rust-side wiring (interpreter dispatch,
JIT/AOT text-arg marshaling) by rebuilding, because the shared
`src/compiler_rust` target dir was under contention from **5 concurrent
`cargo build` processes** from other sessions for the full ~10-minute
bounded wait attempted (`for i in 1..30; do pgrep -f 'cargo build' || break;
sleep 30; done`, per the shared-target-dir coordination protocol — never run
a second concurrent `cargo build --release` against the same target dir).
No free slot opened in that window.

**What IS verified:** the pure-Simple/spec-visible surface (the `.spl`
wrapper, the `detect_virtio_gpu_device` refactor, and the spec docstrings)
is internally consistent and every touched file's diff against
`origin/main` was checked to be a clean, non-destructive addition (no
reverted content). **What is NOT yet verified:** that the new Rust extern
(`rt_file_is_char_device`) actually links, that `nm` shows the symbol in a
freshly built binary, and that the spec's positive/negative branches
(`/dev/null` → true, `/etc/hostname` → false) actually pass end-to-end
through a rebuilt binary — none of that can be confirmed without a build.

**Unblock condition:** once a `cargo build --release` slot is free (verify
via `pgrep -af 'cargo build'` returning empty), from `src/compiler_rust/`
run an INCREMENTAL `cargo build --release` (never clean), confirm
`nm src/compiler_rust/target/release/simple | grep rt_file_is_char_device`
finds the symbol, then run the spec via the freshly built binary:
`src/compiler_rust/target/release/simple run
src/app/test_runner_new/test_runner_single.spl
test/01_unit/os/compositor/vulkan_compositor_backend_spec.spl
--no-session-daemon --sequential` and confirm `Results: N total, N passed, 0
failed`. Do not deploy `bin/simple`/`bin/release/**` from this change alone
without that verification. Separately, re-run
`scripts/check/check-simpleos-wm-fullscreen-evidence.shs` (SIMPLE_BIN pinned
to a stage2 binary, foreground, generous timeout) to confirm
`rt_file_is_char_device` no longer appears in the freestanding
fabricated-stub list and to see whichever symbol/blocker is next in that
gate.
