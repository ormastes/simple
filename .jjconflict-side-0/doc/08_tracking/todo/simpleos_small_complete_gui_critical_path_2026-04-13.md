# SimpleOS Small-Complete-GUI — Critical-Path TODO/Stub Scan

**Date:** 2026-04-13
**Scope:** every file on the Small-Complete-GUI critical path per
`doc/03_plan/simpleos_small_complete_gui_status_2026-04-13.md` and
`doc/03_plan/sys_test/simpleos_small_complete_gui.md` (SYS-GUI-001..006).
**Agent:** Y — Critical-Path TODO/Stub Scan + Close.

This is a tracking doc only, not a feature spec. Follow-ups that need
dedicated agent slices are linked from
`doc/03_plan/agent_tasks/simpleos_small_complete_gui.md`.

---

## Summary

| Metric | Count |
|---|---|
| Raw marker hits scanned on critical path (`TODO|FIXME|XXX|HACK|pass_todo|pass_do_nothing|pass_dn|NotImplemented|STUB|stub|placeholder|fake|mock`) | 60+ |
| Real findings after triage (intentional `pass_dn`/match-default/variable-name `placeholder`/docstring-only excluded) | 7 |
| Closed this slice | 0 |
| Deferred (A — gate-blocking follow-ups) | 4 |
| Deferred (B — critical-path polish) | 0 |
| Deferred (C — explicit next-milestone) | 1 |
| Deferred (D — unrelated drift / upstream bug) | 2 |

**Key observation:** the critical path is already remarkably clean. Most
`placeholder` / `fake` / `pass_dn` hits are either (1) variable names
for SDN `placeholder` attribute, (2) zero-sized struct padding fields
(`_placeholder: i32`) used because zero-field structs are illegal, (3)
docstrings describing fallback behavior that is actually implemented,
or (4) match-default no-ops that are semantically correct. The genuine
silent stubs are all concentrated in one file under another agent's
active edits: `src/os/kernel/ipc/syscall.spl` and one helper on
`src/os/services/wm/wm_service.spl`.

## Category legend

- **(A) Gate-blocking** — required for SYS-GUI-001..006 to pass.
- **(B) Critical-path polish** — on the path but not blocking the 6-test gate.
- **(C) Next-milestone** — relevant but explicitly out of scope per plan.
- **(D) Unrelated drift** — happens to live on the path but is not about the GUI path itself.

## Findings table

| # | File | Line | Cat | Summary | Action |
|---|---|---|---|---|---|
| 1 | `src/os/services/wm/wm_service.spl` | 663 | **A** | `register_launcher_spawn` body is `pass_dn`; comment says "Record the PID so we can match the connect request to this launch notification later" — but nothing is recorded. Connect-side lookup in `parse_create_window` therefore cannot correlate an incoming IPC connect to a launcher spawn, so the WM falls back to heuristics and the SYS-GUI-003/004 ownership-join is weaker than it should be. | **deferred → Agent N (new)** |
| 2 | `src/os/kernel/ipc/syscall.spl` | ~660–665 | **A** | `_handle_ipc_connect` uses a fake `"port"` literal as the connect target name. Real implementation should copy the service name from userspace and look it up in a name table. Blocks reliable multi-process IPC, which SYS-GUI-004 relies on. | **deferred → Agent W (already owns file; extend scope)** |
| 3 | `src/os/kernel/ipc/syscall.spl` | ~1475–1485 | **A** | `_handle_sysinfo` case `2` (Uptime) returns literal 0. `SYS-GUI-001` boot markers and lifecycle debug logs would benefit from real monotonic uptime; currently any `uptime()` call silently returns 0 and tests cannot use it to assert boot-time deltas. | **deferred → Agent W** |
| 4 | `src/os/kernel/ipc/syscall.spl` | ~1865–1875 | **A** | `_handle_lseek` marked `Stub: return the requested offset as-is (no real FD table yet)`. Means `lseek` is a no-op on any real FD: user apps seeking into config files get silent wrong data. Not blocking SYS-GUI-001..006 directly, but blocks `SYS-GUI-007` (storage-backed follow-up) which the plan explicitly mentions. Marked A because the plan lists persistence as milestone-required. | **deferred → Agent W** |
| 5 | `src/os/qemu_runner.spl` | ~1004 | **C** | `TODO(next-milestone): drive one real app-launch that touches FAT32 via VFS`. Explicitly tagged next-milestone; correct state. | **leave as-is, documented here** |
| 6 | `src/os/services/vfs/vfs_init.spl` | 204 | **D** | `TODO(P2/compiler): c_pcimgr_init() skipped — LLVM --no-mangle resolves extern fn to CNvmeBlockAdapter.init (single-module name collision)`. Upstream Rust-compiler extern-fn resolution bug; blocks SYS-GUI-007 storage lane but not SYS-GUI-001..006. Already has a targeted compiler-layer TODO. | **leave as-is, documented here** |
| 7 | `examples/simple_os/arch/x86_64/boot/glass_render.c` | multiple | **D** | 7 `TODO(P3/gpu)` pixel-shader offload markers + 1 stub note on glyph render. Explicitly P3 GPU follow-ups, already documented in the glass_render comment block. File is Agent L/P territory — do not touch. | **leave as-is, documented here** |

## Hits intentionally excluded from the "findings" count

These were reviewed one-by-one and are not stubs:

### Legitimate variable name / struct padding / SDN attribute

- `src/os/compositor/fb_backend.spl:312-315` — reads an SDN `placeholder` attribute; the word is the attribute name, not a stub marker.
- `src/lib/common/render_scene/engine_int.spl:69,73` and `engine_float.spl:112,116` — `_placeholder: i32` is a zero-value padding field so the struct has at least one field. Both engines are real impls of the `EffectEngine` trait.

### Legitimate match-default / else no-ops

- `src/os/desktop/shell.spl:393` — unknown action kind catch-all.
- `src/os/compositor/animation_controller.spl:68` — completed springs are dropped by *not* pushing to `active`; comment is accurate.
- `src/os/compositor/hosted_input_backend.spl:435` — unhandled key variant.
- `src/os/compositor/fb_backend.spl:219` — unknown widget kind catch-all.
- `src/os/compositor/fb_backend.spl:474` — unhandled special key.
- `src/os/compositor/compositor.spl:1180,1190,1214,1234,1248,1344,1963` — match-default catch-alls.
- `src/os/apps/hello_world/hello_world.spl:56,60,61,67,73` — event-match defaults.
- `src/os/apps/browser_demo/browser_demo.spl:74,81,88` — event-match defaults.
- `src/os/services/display/display_service.spl:175,181` — `Ok` arms of `match detach_result` / `match unref_result`; the error arms log, the ok arms are intentionally empty.

### Legitimate docstrings / comments

- `src/os/desktop/shell.spl:149` — docstring about `task_reaper_enabled` in unit tests ("fake PIDs" = description of test scenario, not a stub).
- `src/os/desktop/shell.spl:412` — docstring for `launch_app_baremetal` describing the baremetal overlay path; the implementation is present and working.
- `src/os/desktop/shell.spl:815` — docstring for `_build_app_tree` describing its placeholder fallback for unregistered app names; the fallback is a real implementation.
- `src/os/compositor/text_render.spl:425` — Unicode fallback block-rendering path; real render.
- `src/os/cli.spl:33` — `pass_do_nothing` in `--arch` two-arg branch; the `while` loop below handles the pair form, so the `for` loop's `pass_do_nothing` is correct.

## Files scanned

```
src/os/desktop/
src/os/services/wm/
src/os/services/launcher/
src/os/services/display/
src/os/services/vfs/vfs_init.spl
src/os/compositor/
src/os/kernel/ipc/
src/os/gui/
src/os/apps/hello_world/
src/os/apps/browser_demo/
src/os/drivers/gpu/
src/os/drivers/virtio/virtio_gpu.spl
src/lib/common/render_scene/
src/lib/common/window_protocol/
src/lib/gc_async_mut/gpu/engine2d/backend_virtio_gpu.spl
src/os/cli.spl
src/os/qemu_runner.spl
examples/simple_os/arch/x86_64/desktop_e2e_entry.spl
examples/simple_os/arch/x86_64/boot/glass_render.c
```

## Follow-ups

- **Agent N — WM launcher-spawn PID correlation.** New entry in
  `doc/03_plan/agent_tasks/simpleos_small_complete_gui.md`. Adds a
  `pending_launcher_spawns: [LauncherPendingSpawn]` field on
  `WmService` and wires `register_launcher_spawn` to append, then
  teaches `parse_create_window` to drain the matching entry when a
  connect arrives with the same PID. Small, bounded, no SYS_IPC_*
  constant changes.
- **Agent W — syscall stubs** (items 2, 3, 4 in the table). No new
  doc entry; already Agent W's file ownership.

## How to regenerate this scan

```
grep -rnE '(TODO|FIXME|XXX|HACK|pass_todo|pass_do_nothing|pass_dn|NotImplemented|not wired|not_wired|STUB|\bstub\b|placeholder|\bfake\b|\bmock\b)' <critical-path-files>
```

Then triage each hit against the four categories above.
