# SMUX authenticated protocol feature workflows

**Status: authored manual; execution and generation pending (TEST_BLOCKED).**
Source: `test/03_system/tools/smux_protocol_features_spec.spl`.
There is no admitted general SSpec runner for this Windows checkout. These are
expected workflows, not passing transcripts. SPipe docgen must generate the
manual with zero stubs before verification can accept it.

Audience: maintainers verifying the production line protocol and authenticated
server dispatch boundary. Setup imports `os.apps.smux.api` and creates real
service records without children. `protocol_session(name)` asserts one session,
one window and one pane before returning their actual identifiers.

## Sessions and windows — REQ-SMUX-CORE-001

1. Submit bare `list` to an empty service. Expect `smux: sessions=0`.
2. Create work and monitoring sessions through the API. Bare `list` reports two
   sessions and their identifiers differ.
3. Create a logs window and select it through `select-window work <id>`.
   Work changes focus; monitoring retains its original active window.
4. Select monitoring's window under work. The protocol reports an unknown
   window and both sessions retain their original focus.
5. Run `windows work`. Both work window IDs appear; monitoring's window ID
   does not appear.
6. Select a window under an absent session. The protocol reports an unknown
   session; the existing session and active window remain intact.
7. Request a new window without a name. It refuses before allocating resources.
8. Fill all eight window and pane slots. A ninth protocol window request
   refuses before shell creation and preserves the initial active window.

## Split refusal boundaries — REQ-SMUX-CORE-002

1. Request `split work diagonal`. It refuses without adding a pane, spawning a
   child or changing the original 80 by 24 dimensions.
2. Close the final pane and request a vertical split. It reports no focused
   pane and does not allocate a replacement.
3. Fill the eight-pane service capacity using eight ordinary session records.
   A protocol split refuses with a capacity error; work retains its original
   pane and dimensions.

Successful protocol split/spawn and new-window/spawn are separate live host
acceptance requirements. These refusal scenarios do not prove those paths.

## Active window and pane routing — REQ-SMUX-CORE-003

1. Split work through the API and select its second pane through the protocol.
   Sending a multiword command refuses because this pane has no child. The
   error must name the selected pane ID, proving the first pane was not used.
2. Create and select logs. Sending must name logs' focused pane in its
   no-child refusal, proving the first window was not used.
3. Close the first window's only pane, select populated logs and capture.
   The response is `smux: capture[work]:` followed by a newline and empty
   content. Accessing the first window would fail this oracle.
4. Select logs and run `panes work`. Only logs' pane ID appears.
5. Select a logs pane while the initial window remains active. It reports an
   unknown pane; the initial window's focus remains unchanged.
6. Close the active window's final pane. Both capture and send report no
   focused pane, and the window remains empty.
7. Submit `send work` without command text. It reports the missing argument;
   capture remains empty and pane focus remains unchanged.

## Detach and reconnect — REQ-SMUX-CORE-004

1. Attach and detach a first client, then attach a replacement. Session,
   window and pane IDs survive. The replacement remains independently
   detachable through the production API.
2. Detach a client twice. The first request succeeds, the second refuses;
   the session remains present.
3. Attach a client to work, then detach it under monitoring. The request
   refuses. Detaching it under work succeeds exactly once; monitoring's pane
   remains intact.

## Authentication before dispatch — REQ-SMUX-PROTOCOL-001

1. Submit `secret list` with configured token `secret`. The production server
   boundary returns the actual service session count.
2. Submit `wrong new injected`. It returns `smux: unauthorized` and creates
   no session or shell.
3. Submit a window selection with the wrong token, then the correct token.
   Only the authenticated request changes the active window.
4. Submit detach and stop-server with the wrong token. Both refuse, the
   client attachment remains detachable and the session remains present.
5. Submit an empty supplied token, an empty configured token and an empty
   request. Every request returns unauthorized and creates no session.
6. Append embedded LF or CR to an authenticated new request. Each returns an
   invalid request error before session creation.
7. Submit a request exceeding the 4096-byte limit. It returns an invalid
   request error before session creation.
8. Submit fewer than 4096 characters whose UTF-8 encoding exceeds 4096 bytes.
   The same byte limit refuses the request before session creation.

## Response framing — REQ-SMUX-PROTOCOL-002

1. Decode `SMUX/1 9` followed by a newline and the body `café`, a newline,
   and `界`. The nine UTF-8 body bytes decode to the original multiline text.
2. Decode a zero-length body. The result is an empty string.
3. Declare five bytes and provide only three before EOF. Decoding refuses
   the incomplete response.
4. Declare three bytes and provide four. Decoding refuses the trailing data.
5. Supply raw unframed output or a header without its terminating newline.
   Each refuses with an invalid header error.
6. Supply a negative length. Decoding refuses with an invalid length error.
7. Declare 65537 bytes, exceeding the 65536-byte reply limit. It refuses.
8. Supply a nonnumeric length. Decoding refuses with an invalid length error.

These codec scenarios call the production byte decoder directly. They prove
no socket reads, writes, fragmentation, deadlines or listener behavior.

## Named layout and composite screen — REQ-SMUX-PROTOCOL-003

1. Split a real production session through the API. Select `even-horizontal`
   on a 12 by 6 canvas. `rects` reports each actual pane ID: the first owns
   `(0,0,6,6)`, the second `(6,0,6,6)`. Both pane grids have six columns.
2. Change to `even-vertical`. The same IDs own `(0,0,12,3)` and
   `(0,3,12,3)`; focus remains on the original pane.
3. Capture the empty two-pane screen from production cell snapshots. Its body is exactly six rows of twelve
   spaces, joined by newlines. The production capture count increases by two,
   verifying one capture per pane for this composition.
4. Select a second window with a 4 by 2 tiled canvas. `rects` uses its pane ID
   and `screen` contains two rows of four spaces. Return to the original
   window; its independent 12 by 6 geometry survives.
5. Change work's layout. Monitoring retains its manual layout and original
   80 by 24 pane dimensions; its rectangle uses the real pane ID and full canvas.
6. Capture a manual window before selecting named geometry. Persisted geometry
   permits screen capture, rectangles show the real full-canvas pane, and the
   capture count advances once without changing the layout.
7. Select a valid layout, then request an invalid name. The request refuses;
   the selected layout and exact prior rectangles survive.
8. Request two column bands in a one-column canvas. It refuses without
   changing the selected rectangles.
9. Submit missing, nonnumeric, zero and negative dimensions. Each refuses
   without changing the manual layout or original dimensions.
10. Exceed 512 columns, 256 rows and 60000 cells independently. Each refuses
    before pane resize.
11. Select canvases exactly at 512 columns, 256 rows and 60000 cells. Each
    succeeds with its actual requested pane dimensions.
12. Feed CJK text into real VT cells. Compose two four-column panes and verify
    the exact output plus sibling marker at display column four. The wide
    character retains its empty continuation cell.
13. Repeat with a two-cell emoji. The sibling marker still begins at column
    four, and the exact composite string retains the emoji.
14. Capture a complete CJK glyph, then compose into a narrower two-column
    rectangle that clips its continuation. The orphan leading half becomes a
    blank, the sibling marker starts at column two and the input cells survive.
15. Feed a decomposed accented character through the real VT parser. Its
    combining mark remains in the original cell; exact composition and a VT
    readback retain both accent and sibling column.
16. Feed the upper wide-range endpoint U+115F followed by U+0301. The combined
    cell remains width two when classified by its first scalar, retains its
    continuation and preserves the sibling marker at column four.

The service geometry checks call production cell-snapshot capture and
composition, preserving complete cells rather than flattening pane text before
placement. The five Unicode helper checks call `vt_feed(vt_new(...), raw)` through `protocol_cells`
and production layout/composition helpers, then assert exact strings and VT
readback cells. They prove cell placement and explicit composite row writeback;
they prove no process execution, visible terminal drawing, child terminal
resize notification or external TUI interaction. Named layouts use the current
gapless rectangle policy; split separator geometry is a separate API contract.

## Reply status — REQ-SMUX-PROTOCOL-004

1. Classify actual successful list, windows, panes, capture, layout, rectangles
   and screen replies. Each is accepted.
2. Classify successful response prefixes, including captured text containing
   error messages and `(no shell:)`. Pane content must not turn a successful
   capture into a failed command. The supplied successful creation, selection,
   attachment, split, send and stop response texts are accepted.
3. Classify actual usage, unknown session/pane, missing attachment, no-child,
   invalid layout size and manual-screen refusal replies. Each is rejected.
4. Classify supplied no-shell creation, capacity, spawn, layout usage/failure,
   authentication, invalid request and empty responses. Each is rejected.

The supplied-response cases exercise only the production status classifier;
they do not claim those shells, clients, failures or stop actions occurred.

**Evidence boundary:** 57 authored scenarios; none executed. These are
source-contract checks of the production dispatchers. They do not prove a
bound listener, remote access policy, persistent owner liveness, idle background
draining, live ConPTY output, separate client processes or rendered screens.
No protocol capture or executable evidence has been produced yet.

Required execution after runner admission:

```text
<admitted-runtime> test test/03_system/tools/smux_protocol_features_spec.spl --native-backend=llvm --assert-ran --keep-artifacts
<admitted-runtime> spipe-docgen test/03_system/tools/smux_protocol_features_spec.spl --output doc/06_spec --no-index
<admitted-runtime> sspec-maintain scan test/03_system/tools/smux_protocol_features_spec.spl
```

Record the exact runtime/producer identity, supported command switches,
executed case counts and exit status. Source discovery is not execution.
