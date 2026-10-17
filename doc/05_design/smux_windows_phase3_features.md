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
zero-timeout read chunks per poll. Input and terminal query replies share a
65536-byte retained queue per pane. A flush offers at most 4096 bytes and keeps
the exact accepted byte offset; failed writes remain visible through
`input-status SESSION`. Queue acceptance does not certify child delivery.
Native Windows overlapped input is authored; execution under a child that
refuses input remains a required fairness gate.

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

`history SESSION [LINES]` serializes retained primary-screen cell rows and the
current synchronized screen snapshot, with a default request of 200 lines and
a remote maximum of 2000. Alternate-screen scrolling and partial scroll regions
do not enter primary history. CSI 3J clears saved rows, CSI 2J preserves them,
RIS resets them, and resize retains them. Scrollback retrieval does not yet
provide interactive copy/selection mode.

The ordered Windows-native source overlay selects actual Winsock and ConPTY
owners through stable library imports. See
`doc/07_guide/tooling/smux_windows_native_composition.md`. Native resize must
succeed before VT/service metadata commits; named multi-pane resizing attempts
rollback on failure and reports incomplete rollback explicitly. Dimensions are
validated before narrowing to Win32 terminal coordinates or grid allocation.
After initial native close calls, the server polls deferred PTY cleanup for at
most two seconds; this does not prove a total shutdown bound. An outer watchdog
must supervise close as well as backpressure. During that polling,
unreleased resources or socket close errors prevent a successful shutdown exit.

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

## Interactive terminal client (authored, not qualified)

`--attach ENDPOINT TOKEN SESSION CLIENT_ID` registers a client and acquires a
console lease through `std.sys.terminal_console`. The Windows native overlay
selects a direct Win64 console owner; the default facade reports unsupported.
This preserves the same hosted app and controller for every host provider.
Terminal input is nonblocking and bounded; output enables terminal VT rendering
and cleanup attempts to restore both original console modes on every exit.

Each controller stores its selected window and pane locally. `client-panes`,
`client-layout`, `client-split`, `client-history`, `input` and `frame` carry an
explicit window, with pane targets where needed. Input is strict complete UTF-8
encoded as hex and never gains an implicit newline. Frames contain a validated
canvas header and server-generated cursor/SGR sequences from a real VT snapshot;
raw child OSC/control strings are not replayed. The snapshot freezes cursor
position/visibility along with cells and styles during synchronized output.

Ctrl-B d detaches; c creates a window; n cycles windows; o cycles panes;
percent splits columns; double quote splits rows; Space cycles the five layouts.
Ctrl-B Ctrl-B sends a literal prefix; unknown bindings preserve both bytes.
Ctrl-B left bracket enters a local history viewport; k/j or arrow/page keys
scroll, and q or Escape leaves it. Space marks a line and Enter or y copies the
selected line range through the native clipboard capability, then leaves copy
mode. Clipboard writes happen only for that explicit user action. Old wider
history rows clip by terminal cells after resize. Ctrl-B k/j/q also
navigate/leave that viewport.
Interactive history retains the newest complete lines within the response byte
budget, including the header; requesting 2000 dense rows does not require an
oversized response. The public explicit history command retains its separate
limit/error contract. A single newest line exceeding the whole byte budget is
an explicit error rather than invalid UTF-8 truncation.
This is an initial binding table, not exact tmux configuration compatibility.
The client polls frames every 50ms and sleeps 10ms between bounded turns;
actual latency/CPU/RSS must be measured rather than inferred from these values.

Viewport changes on one client do not choose another client's selected window.
Clients register actual dimensions through `client-size`; shared window frames
use the smallest attached dimensions for that session, preserving the selected
named layout and reflowing only when its canvas changes. A detached small client
no longer constrains the next frame. Clients additionally refuse a frame larger
than their current terminal and clear padding after canvas changes. Copy keys
decode incrementally across fragmented/coalesced reads; standalone Escape has
an explicit 100ms disambiguation delay. Mouse, configurable key tables, automatic owner
launch/discovery and full control-mode compatibility remain outstanding.
Manual geometry also reflows before a sibling frame, including the interval
between a successful split and the requesting client's next layout command.
Unexpected client crashes can still leave attachment records; heartbeat/lease
expiry is an outstanding lifecycle gate.

## Native SSpec provider selection

The native runner accepts repeated `--native-source PATH` selectors in order.
For this cohort, select the Windows overlay before `src/app`, `src/lib`,
`src/os` and `src/compiler`. The canonical runner owner validates up to five
existing directories, forces native execution without unbound result reuse,
and forwards those roots through worker arguments into native-build's ordered
`--source` arguments. Invocation receipts, native artifact identity and metrics
cohorts bind the ordered selector identity. Configured family facades continue
delegating to the common concrete owner; no GC family is globally pinned.

`--native-backend=llvm` alone cannot select the Windows providers, and
`SIMPLE_LIB` affects interpreter lookup rather than this native AOT path. The
ten new source-root contract scenarios and their authored manual remain
unexecuted. Rebuild/admit the actual runner before using the new flags as
Windows test evidence. See `doc/07_guide/infra/testing/native_test_binary_workflow.md`.

## Precise sleep dependency

The owner and interactive client import `concurrent.thread.thread_sleep` as
`thread_sleep_ms` directly. This is the same public function formerly selected
by the I/O facade; the facade has no initialization or wrapper behavior to
retain. Under the compiler's module-transitive entry closure, this avoids
unrelated synchronous/asynchronous buffer bodies. Astra accepted this dependency
design. The diagnostic closure shrank from 117 to 92 modules; that is a source
inventory observation, not a runtime or performance PASS.

The canonical server retains `client.stream.close().is_err()` for verification
with the declared-field receiver compiler repair. The private diagnostic's
local stream-copy substitution is not a product change. Match closure capture
and field-result typing have separate compiler regressions; unsupported
cross-trait casts remain an open compiler issue.
