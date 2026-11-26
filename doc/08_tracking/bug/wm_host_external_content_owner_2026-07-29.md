# Host external content ownership

Status: rendering overwrite fixed; remote application presentation implemented
and verified on the resident headless WM daemon lane only (2026-11-26). Owner decision
2026-11-26: in scope for release 1.0.0. Three follow-ups remain open, listed at
the end.

## Root cause

`HostCompositor.requires_external_web_frame()` inferred BrowserRenderer ownership
from `owner_port > 0`. A validated GUI or pixel `WmContentFrame` therefore
remained eligible for a later Web frame overwrite.

## Fix

Hosted windows now carry one scalar `content_owner`. Creation assigns local
Web, remote Web, or browser ownership. Validated GUI/pixel frame admission
changes that owner, lifecycle mutations preserve it, and releasing the frame
restores the creation default. BrowserRenderer eligibility now depends only on
the scalar owner.

## Remote application presentation (2026-11-26)

Plan: `doc/03_plan/ui/wm_remote_app/remote_app_presentation_plan.md`.

The compositor needed no change. What was missing sat outside the process, and
is now a transport around the resident headless WM (`app.play.wm_daemon`):

- `src/lib/nogc_sync_mut/ui/wm_remote_surface.spl` — the shared present slot:
  one `MAP_SHARED` file of exactly `w*h*4` ARGB32 bytes, no header.
- `src/app/play/wm_remote_app_client.spl` — what an application links.
- `src/app/play/wm_remote_app_host.spl` — WM-side systems over a table of
  surface rows: open, present (full or damage rectangle), input routing with a
  bounded queue, frame probe, liveness reap.
- Verbs 6..10 in `wm_daemon_client.spl`; the serve loop routes them.

The present message is the publication point: the WM reads the slot only while
handling it and the client waits for the reply before writing again, so there
is no concurrent access, no lock and no atomic. No new `rt_*` symbol.

Evidence on this host (aarch64 Linux, seed
`cargo-target-wr-seed1126b/release/simple`, sha256 `fb80903917d6d5f5…`):

- `test/03_system/gui/wm_host_platform/wm_remote_app_two_process_spec.spl` —
  three real processes. WM pid 866470, client pid 871200, controller pid
  866317. The client fills 200x120 with `0xFF12AB34`; the WM's framebuffer
  readback holds exactly 24000 pixels of that colour, all inside the window's
  content rect; framebuffer hash `1312651653978070631` before,
  `1312651653979251297` after. No client: 0. Corrupted checksum: refused
  (`checksum-mismatch`), 0. Client killed: window and slot gone, 0.
- `test/02_integration/app/wm_remote_app_presentation_spec.spl` — 6 examples
  through the production route in one process (present, checksum refusal,
  stale revision / not-owner, damage, input, reap).
- Red first: without the new modules the spec fails to resolve
  `app.play.wm_remote_app_client`. Mutation: making the client skip the slot
  write turns 3 of the 6 examples red.

## Still open

1. The windowed host (`src/os/hosted/hosted_entry.spl`, SDL2) has no request
   pump: it seeds windows in-process and never reads client messages, so only
   the resident headless WM serves the remote verbs.
2. The hosted SDL2 event loop (`host_gui_event_router.spl`) does not yet call
   the `surface-input` route for a remote-owned window; only the injection
   verb does. Not verifiable on this host (no display server).
3. A WM-side resize does not reallocate the slot; the last frame stays until
   the client reopens.

Separately observed, not caused by this change: on the release-head seed the
compositor module graph does not lower through the JIT
(`SPL-UNIT-002: Count Add <scalar>`), so `simple play daemon …` only runs with
`SIMPLE_EXECUTION_MODE=interpreter`, and the transport's round trip is bounded
by `daemon_sdk`'s 100 ms client poll.

## Linux aarch64 re-check (2026-11-26, lane wm-lane-20261126)

release/1.0.0 79445b063c4, seed
`/home/yoon/.cache/cargo-target-wr-seed1126b/release/simple`:
`simple run test/fixtures/wm_host_content_owner_probe.spl` exits 0 (negative control: flipping its first comparison exits 1), so the
scalar owner helpers (`host_content_owner_default`/`_for_frame`/`_requires_browser_renderer`) still behave; no frame evidence was captured. None of the remaining pieces exists
in `src/os`: no pixel-present window-protocol command, no bounded present
slot or scalar host bridge, no remote GUI/pixel event receiver, and no
deployed native server poll. Building them is feature work, not a bug fix.
The row stays open on the 2026-11-04 owner question: is remote application
presentation in scope for 1.0.0, or should it move to a feature request?
