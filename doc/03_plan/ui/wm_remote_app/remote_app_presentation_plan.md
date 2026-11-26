# Remote application presentation in the Linux-hosted WM

Bug: `wm_host_external_content_owner_2026-07-29`. Owner decision 2026-11-26:
in scope for release 1.0.0.

## Finding

The compositor already admits a validated pixel `WmContentFrame`
(`HostCompositor.set_external_content_frame`, owner becomes `PIXEL`). What is
missing is everything outside the process: no pixel-present command, no shared
surface, no remote event receiver. `HostCompositor` therefore needs no change;
the work is a transport around the resident headless WM (`app.play.wm_daemon`),
which already serves window open/close over `std.daemon_sdk` file messages.

## Shape (MDSOC+)

Outer feature module `wm_remote_app`; the business layer follows the ECS
shape: the entity is the window id, its one component is a plain surface row
(slot path, size, client pid, last revision, pending events), and open,
present, input and reap are systems over the row table. It is a plain row
table, not a `std.ecs` `World`: with a single component type there is no
query to express, and the table has to be handed back by value (see
`WmRouteOutcome`). No object graph, no shared mutable state between
processes.

| part | file |
|------|------|
| slot (pixels only) | `src/lib/nogc_sync_mut/ui/wm_remote_surface.spl` |
| host systems + rows | `src/app/play/wm_remote_app_host.spl` |
| client library | `src/app/play/wm_remote_app_client.spl` |
| verbs, serve loop | `src/app/play/wm_daemon_client.spl`, `wm_daemon.spl` |

## Transport — no locks, no atomics, no new `rt_*`

- Surface: one file per window, exactly `w*h*4` bytes of ARGB32. The client
  maps it `MAP_SHARED` (`rt_mmap`). The WM never maps the slot: it copies it
  with ordinary reads into a private snapshot and maps only that, so a
  client truncating its slot cannot fault the WM. It carries no header.
- **The message is the publication point.** All metadata (size, content
  revision, checksum, damage) travels in the `surface-present` request. The WM
  reads the slot only while handling that request; the client does not write
  again until the response arrives. Ownership of the slot alternates by
  message, so there is never a concurrent reader and writer and no
  cross-process memory-ordering assumption (the host is aarch64).
- Verbs: `surface-open` (6), `surface-present` (7), `surface-events` (8),
  `surface-input` (9), `frame-probe` (10). Existing verbs are unchanged.

## Ownership and lifetime

The WM creates, sizes and deletes the slot; the client only maps it. Slots
live in a per-daemon-instance directory (`mkdtemp`, mode 0700, random name),
so a client left over from an earlier daemon cannot write into a new
daemon's `window_1`. A slot lives exactly as long as its window: removed on
`window-close` and on reap; the instance directory is removed on daemon
stop, and directories left by a crashed daemon are swept at the next start.
The WM holds no mapping between presents. Size is fixed at open; a WM-side
resize keeps the last frame until the client reopens (slot reallocation is
not in this change).

## Damage

Optional `damage=x,y,w,h` on present. The WM reads only those rows and feeds
the existing `base_content_revision` / `damage_rects` / `damage_pixels` path,
which already rejects a delta whose base revision is not the retained one.

## Input routing

`surface-input` (the injection seam the headless WM needs; the hosted event
router does not call it yet, see Waves) hit-tests the content
rect top-most first, converts to window-local coordinates, and appends to that
row's bounded queue (64; overflow drops the oldest and counts it). Keys go to
the focused window. The client drains with `surface-events`. The verb accepts
only the kinds move/button/key and only from the pid that owns the target.

## Failure modes

| failure | behaviour |
|---------|-----------|
| checksum / size / revision mismatch | present refused with a reason; prior frame kept |
| slot missing, wrong length, or truncated mid-read | refused by length of the private copy; the WM never maps the slot, so no SIGBUS |
| client dies | pid liveness reap: window destroyed, slot deleted |
| WM dies | client request times out; its mapping stays valid, nothing blocks |
| unknown window / pid differs from the opener's | refused |
| pid <= 1 or not running at open | refused (`bad-pid`) |
| one pid holds 16 surfaces, or 64 exist | open refused (`too-many-surfaces`) |

**Trust boundary: the user id.** The `daemon_sdk` file transport carries no
peer credential, so the client pid in a request is client-supplied. It is a
liveness handle and a guard against accidents between well-behaved clients,
not authentication: any process of the same user can already read and write
the request directory and the slots. The slot directory is under
`$XDG_RUNTIME_DIR` when set (0700 tmpfs), otherwise the daemon cache
directory; the instance directory itself is always 0700.

## Evidence gate

`test/03_system/gui/wm_host_platform/wm_remote_app_two_process_spec.spl`
(a spec, not a wired gate script): start the WM daemon (PID
A) and a separate client process (PID B). B draws a known colour and presents.
`frame-probe` renders through the production `HostCompositor` + headless
backend and returns the framebuffer hash and the count of that colour. Pass
needs count == w*h and a hash that differs from the pre-present hash. Negative
controls: no client gives count 0; a corrupted checksum is refused and leaves
count 0; a killed client removes the window. Both PIDs are printed.

## Waves

1. Slot + present + probe + two-process gate (red spec first).
2. Input queue, damage, reap.
3. Not in this change:
   - the windowed host (`src/os/hosted/hosted_entry.spl`, SDL2) has no
     request pump, so only the resident headless WM serves these verbs;
   - `host_gui_event_router.spl` does not forward to `surface-input`
     (no display server on the verification host);
   - slot reallocation on resize.

Perf: zero remote clients costs one length check per serve cycle; compositor
frame time A/B must stay within 2%.
