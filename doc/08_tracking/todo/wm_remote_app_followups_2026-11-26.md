# TODO: remote application presentation follow-ups

Bug: wm_host_external_content_owner_2026-07-29
Plan: doc/03_plan/ui/wm_remote_app/remote_app_presentation_plan.md
Filed from the wave 2 review, 2026-11-26. None of these is done.

## 1. A present copies the whole slot on the frame thread (P1, perf)

`wm_remote_surface_read_rect` (`src/lib/nogc_sync_mut/ui/wm_remote_surface.spl`)
snapshots the entire slot with `file_copy` before reading, for a full frame
and for a damage rectangle alike. At the admitted maximum (8192 x 8192) that
is 256 MB per present, done inside the request handler that the compositor's
frame loop runs.

Wanted: copy only the bytes the present needs. A damage present should read
just the damaged rows; a full present should read once, not copy and then
read. The read must stay SIGBUS-proof, i.e. it must not map the client's
slot. That needs a positional bounded read into raw memory, which no
existing `std` wrapper provides; a new `rt_*` for it needs both the C and
the Rust lane.

Acceptance: a spec that presents a 16 x 16 damage rectangle on a large
surface and shows the bytes read are proportional to the rectangle, plus the
existing truncated-slot case still refused.

## 2. A remote window gets no input before its first accepted present (P2)

`HostGuiEventRouter.remote_input_target`
(`src/os/compositor/host_gui_event_router.spl`) recognises a remote window by
`content_owner == HOST_CONTENT_OWNER_PIXEL`, and the owner only becomes PIXEL
when the first frame is admitted. Between `surface-open` and that frame,
pointer and key events over the window are not queued for the client.

Wanted: ownership for input decided by the surface table (the window has a
remote surface row), not by whether a frame has arrived.

Acceptance: `hosted_remote_app_input_spec.spl` gains a case that opens a
surface, sends a button event before any present, and finds it in the queue.

## 3. The forwarded key space is undocumented (P2, docs)

`hosted_remote_app_pump_key` (`src/os/hosted/hosted_remote_app_pump.spl`)
forwards `rt_winit_event_key_keycode` values unchanged, so the `key` field of
a `key|0|0|<key>|<action>` row is a winit keycode on the windowed host, while
the `surface-input` verb passes through whatever integer the injector sent.
A client cannot tell which key space it is reading, and no modifier state is
carried.

Wanted: one documented key space for the event row (and the translation at
the pump if it is not winit's), the action values, and a statement about
modifiers, in the plan and in the client module's `wm_remote_app_poll_events`
doc comment.
