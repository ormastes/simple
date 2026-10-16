# SMUX Windows detail design

The compiled client supports `--serve ENDPOINT TOKEN` and
`--request ENDPOINT TOKEN COMMAND ...`. The first explicitly owns service
lifetime; the second is disposable. No-argument stdin mode remains a separate
legacy lifetime with EOF shutdown. New startup paths do not compile or spawn
an owner implicitly.

An endpoint must be `127.0.0.1:PORT`, with a positive port at most 65535. Tokens
are nonempty, at most 128 text units and contain no whitespace. The request
is `TOKEN COMMAND\n`. The complete command frame is at most 4096 bytes;
embedded CR/LF and pipelined frames are refused before dispatch. Responses are
`SMUX/1 BYTE_COUNT\nBODY`; consumers validate exact body length at EOF.

Per-client capacity is 16, each request/reply phase has a two-second absolute
deadline, each turn reads/writes at most one 4096-byte chunk per connection,
and reply bodies are capped at 65536 bytes. The owner accepts with a 10ms
timeout so it continues draining output while idle. Each pane has eight
zero-timeout read chunks per poll. Blocking PTY input/query replies remain a
provider gap and must not be hidden behind these numeric limits.

Commands include new/list, active-window/pane send/capture, windows/panes,
select-window/select-pane, new-window/split, attach/scoped-detach,
`layout SESSION NAME COLS ROWS`, `rects SESSION`, and `screen SESSION`.
Screen capture uses the selected production geometry and one cached cell-grid
snapshot per pane. Wide glyph continuation cells remain empty slots, so padding
and sibling placement use terminal cells rather than encoded string length.
An orphan wide glyph at a clipped edge is replaced by a blank. The exported
VT width helper retains the existing emulator's width policy; this does not
introduce a full grapheme-cluster or Unicode-version compatibility claim.
The result is a plain-text frame, not an interactive terminal UI.

The remote canvas is at most 512x256 and 60000 cells. Directional split/spawn
failure closes the new pane, restores the old pane size and reselects its
previous named plan. Failed creation may still report a retained no-shell
window/session; command status must be nonzero and must not claim success.
`smux_remote_reply_ok` centralizes success classification for request clients.
The cell limit and byte reply limit are independent: UTF-8 screen content may
exceed the reply byte limit even on an accepted canvas, producing an explicit
reply-limit error instead of a truncated successful frame.

Traceability, pending manuals and real Windows process tests belong to
`doc/03_plan/sys_test/smux_windows_phase3_features.md`. Until those scenarios
execute on the exact admitted artifacts, the result remains TEST_BLOCKED.
