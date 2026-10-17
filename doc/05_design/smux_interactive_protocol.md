# SMUX explicit-target interactive protocol

Status: source authored; **TEST_BLOCKED** for compilation, execution and docgen.
These contracts support the same hosted application's interactive client and
independent foreground owner. They do not establish a qualified native binary.

## Requirements and boundaries

- `REQ-SMUX-INTERACTIVE-002`: forward exact complete UTF-8 input, including
  control bytes, without implicitly submitting a command.
- `REQ-SMUX-INTERACTIVE-004`: expose a bounded frame from actual production VT
  cells, styles and cursor, preserving synchronized-output consistency.
- `REQ-SMUX-INTERACTIVE-003`: address explicit windows/panes without
  changing session-global focus on behalf of another client.

`interactive_protocol.smux_interactive_dispatch(line)` returns empty only for
unhandled command names. It resolves a session name or ID, validates the full
session/window/pane relationship, and invokes production service APIs. The
authenticated owner transport retains its existing request/reply byte limits.

| Command | Result |
|---|---|
| `client-size SESSION CLIENT COLS ROWS` | Register/update the actual attachment size without stealing another session's client identity |
| `input SESSION WINDOW PANE HEX` | `smux: input accepted` after bounded queue acceptance; does not claim child delivery |
| `frame SESSION WINDOW [CURSOR_PANE]` | `SMUX-FRAME/1 COLS ROWS` followed by newline and bounded safe ANSI |
| `client-panes SESSION WINDOW` | Existing `smux: panes[...]` listing format |
| `client-layout SESSION WINDOW NAME COLS ROWS` | Existing layout success prefix, explicit target window |
| `client-split SESSION WINDOW PANE DIRECTION` | Create actual pane/PTY, or report failure and any incomplete rollback |
| `client-history SESSION WINDOW PANE LINES` | Existing history prefix with explicit target and 1..2000 line bound |

`NAME=current` retains the window's existing known named layout while updating
canvas dimensions; an initial manual window selects tiled. Initial attach and
resize therefore preserve the owner's existing layout choice. No handler
changes active-window or focused-pane selection. A split invalidates its named
layout through the production API; the client then reapplies the current plan.

## Shared canvas across different terminal sizes

`client-size` records current dimensions in the authoritative attachment table.
`smux_list_clients` exposes exactly the live prefix of its four slots, without a
second mutable size registry. Invalid/nonpositive or remotely oversized updates
are refused. Reusing an existing client ID from another session is refused.

`client-layout` clamps requested dimensions to the smallest positive dimensions
among attached clients of that session. Every `frame` request recomputes that
minimum from current attachment state and reflows the existing named layout only
when the window canvas differs. This covers a smaller terminal attaching,
resizing, or detaching, including expansion to the remaining larger terminal.
An initial manual layout uses tiled; no attached clients retain the existing
canvas. Other sessions have no influence. Impossible pane geometry reports the
actual layout failure instead of transmitting a frame that wraps.

Controllers must report their actual dimensions before layout/frames and reject
a stale frame exceeding the console's dimensions. The registered minimum is
authoritative for interactive frame geometry: a manually smaller layout request
while larger client sizes remain registered may expand back to their minimum
on the next frame. This source behavior requires real differently sized native
console clients for runtime admission; metadata tests alone cannot establish it.

Input is nonempty, at most 1024 decoded bytes, and encoded as exactly two ASCII
hex digits per byte. Complete UTF-8 validation rejects overlongs, continuation
errors, truncation, surrogates and code points beyond U+10FFFF before decoding.
CR, LF, NUL, ESC and ordinary UTF-8 scalars remain data. No token rejoining or
implicit Enter byte changes the payload. Larger pastes must be chunked at UTF-8
scalar boundaries by the client; queue overflow remains a typed failure.

## Snapshot ownership

`api.smux_capture_frame` validates window ownership, optional cursor pane,
selected layout and the remote canvas limits before I/O. It copies `_svc`,
drains at most eight chunks per pane in that window, takes one frame snapshot
from the resulting state and commits `_svc` exactly once. It increments the
capture metric once per valid capture attempt. Drained bytes remain committed
even if the final serialized frame exceeds the reply limit.

`frame_snapshot.smux_frame_from_state` is a pure projection. It reads each
pane's actual VT grid and canonical per-cell SGR, keeps wide continuation cells
aligned within their own pane rectangle, fills the complete canvas and emits
explicit row cursor positioning. It emits only generated CSI cursor/visibility
and SGR sequences; child OSC/control strings and malformed style escapes cannot
reach the client terminal. A cursor pane may be selected independently per
client; omitted selection uses the service's focused pane.

During DEC mode 2026, cells, styles and cursor coordinates/visibility all come
from the same latched completed frame. `VtScreen` now stores frozen cursor
fields alongside its existing frozen cells/attributes. The first mode-enable
latches them; repeated enable does not overwrite them. Mode-disable or screen
resize stops using the frozen frame.

Remote dimensions are bounded to 512 columns, 256 rows and 60000 cells. The
serializer reserves 86 bytes inside the 65536-byte reply bound for its final
cursor sequence. Overflow returns a protocol error instead of truncated ANSI.
Per-pane output may be newer than another pane's preceding read, but every
visible per-pane grid/style/cursor is a coherent production snapshot, and the
single service commit prevents observation of partial API state.

## Evidence required

The unit spec covers strict input bytes and production VT/frame projection,
including malicious snapshot fields, synchronization and bounds. The service
spec drives actual public API and dispatcher behavior, checks one capture
increment, foreign-owner rejection and independent selection/layout retention.
The native Windows scenario starts a real command shell, sends arithmetic
without CR, proves no result, then sends separate CR and requires the actual
computed result. It also captures that output through the frame protocol and
requires terminal cleanup.

All three specs and their authored manuals are pending the qualified rebuilt
runner. Required native Phase2 and Phase3 execution, positive assertion counts,
producer identities and actual Windows terminal-client rendering evidence are
separate from source review. No source-only PASS or dummy provider substitutes
for them.
