# SimpleOS Small Complete GUI — Agent Task Breakdown

## Goal

Parallelize the work needed to close the first `x86_64` QEMU-backed SimpleOS GUI OS milestone.

## Agent 1 — Desktop integration lane

Own:

- real desktop entry selection
- `x64-desktop-test` scenario alignment
- serial-marker-based desktop integration coverage

Deliver:

- one authoritative desktop integration path
- one serial-only regression lane with actionable logs

## Agent 2 — App ownership and lifecycle

Own:

- `Hello World` single-window path
- `Browser Demo` multi-window path
- graceful exit, terminate, and crash cleanup validation

Deliver:

- stable launcher-owned `app_id` across launcher, shell, WM, and compositor
- live lifecycle assertions

## Agent 3 — GUI framebuffer verification

Own:

- QMP framebuffer capture integration
- desktop baseline recording and compare
- tolerance profile selection for the desktop capture

Deliver:

- one desktop QEMU spec with screendump and baseline compare
- baseline artifact and update procedure

## Agent 4 — Storage-backed follow-up

Own:

- disk-image boot path
- desktop boot with storage enabled
- one storage-backed app-launch smoke

Deliver:

- next-milestone proof that the desktop path still works on the intended persistent environment

## Agent N — WM launcher-spawn PID correlation

Source: critical-path TODO scan
(`doc/08_tracking/todo/simpleos_small_complete_gui_critical_path_2026-04-13.md`
finding #1).

Own:

- `src/os/services/wm/wm_service.spl` `WmService.register_launcher_spawn`
  and the connect-side correlation in `parse_create_window`

Problem:

- `register_launcher_spawn` currently ends in `pass_dn`. Its docstring
  says "Record the PID so we can match the connect request to this
  launch notification later" — but nothing is actually recorded, so
  the WM has to fall back to heuristic ownership matching when an
  app's `COMP_CREATE_WINDOW` arrives. That weakens SYS-GUI-003 and
  SYS-GUI-004's "stable launcher-owned `app_id`" assertion.

Deliver:

- new `struct LauncherPendingSpawn { pid: u64, app_name: text, ts: u64 }`
  plus a `pending_launcher_spawns: [LauncherPendingSpawn]` field on
  `WmService`
- `register_launcher_spawn` appends a record
- `parse_create_window` drains the matching pending entry (by PID) and
  uses its `app_name` as the new `WindowOwner.app_id`
- prune stale entries on a short TTL or bounded ring to keep the
  list from growing in crash-loop scenarios

Do NOT touch:

- `SYS_IPC_*` constants in `wm_service.spl` (Agent W)
- syscall dispatcher or `syscall.spl` (Agent W)

Scope: small, local, self-contained; about 40 lines of real code.
Validate with `bin/simple lint` on `wm_service.spl` and the existing
WM unit spec. Do not invent a new gate test — reuse SYS-GUI-003/004.
