# Windows smux / tmux feature audit — 2026-10-16

**STATUS: FAIL for major tmux parity; Windows runtime qualification unverified.**

Independent review of `release_phase3` plus the current admission/split fixes in
`work/smux-windows-phase3-20261016`. This report records source inspection, not
successful execution. No compiler, terminal, or ConPTY test was executed by this
reviewer. Parent-session runtime evidence must be reported separately.

The [official tmux manual](https://github.com/tmux/tmux/blob/master/tmux.1)
was fetched through context-mode on this date, indexed as
`smux-windows-audit-official-tmux-manual`. Its description establishes detached
background execution and later reattachment as core behavior; its session,
window/pane, copy-mode, and key-binding sections define the comparison surface.

Short source filenames below belong to `src/os/apps/smux/`; `cs_dashboard.spl`
belongs to `src/app/llm_caret/`.

| Severity | Finding and concrete evidence | Minimum fix / acceptance evidence |
|---|---|---|
| P1 | No persistent detached owner or reconnect protocol. `api.spl:238` manages in-process client records; `smux_remote.spl:73-78` stops on EOF and resets/kills children. | Separate persistent owner and client transport. Disconnect client A, retain child PID, reconnect B, verify output produced while detached. |
| P1 | Background output can stall: `cs_dashboard.spl:545-548` documents that children fill their PTY buffers unless capture drains them. `api.spl:169` drains on API access. | Owner continuously drains all panes without clients. Produce output larger than pipe capacity while detached and prove child completion. |
| P1 | Live resize does not reach the child: `api.spl:371-377` updates pane/VT metadata only. | Add provider resize and propagate geometry. Query Windows `mode con` before and after resizing an already-running child. |
| P1 | System evidence substitutes local service functions: `test/03_system/tools/smux_system_spec.spl:34-43,183-197` claims API coverage while send checks only identity and capture returns `captured`. | Exercise production API and independent child-generated nonces; count model tests separately. |
| P1 qualification gap | Windows ConPTY exists in `src/compiler_rust/runtime/src/value/pty.rs:206,284,364`; `src/lib/nogc_async_mut/sosix/pty.spl:3-8` explicitly says core-C stage-3 cannot resolve these Rust-only symbols. | Demonstrate the designated self-hosted Windows artifact spawning/capturing/closing a real ConPTY; implement missing provider symbols if linkage fails. |
| P2 | Splits now change dimensions, but no persistent split tree/offsets or automatic child spawning is connected to `api.spl:322`; windows are metadata operations (`:265,287`). | Wire layout/rendering and shell lifecycle; verify two independent visible panes, window switching, and resize. |
| P2 | PTY scrollback is absent: `_drain` feeds only the screen; `service.spl:75-85` captures the current grid. Copy-mode, mouse, key-table/config/control compatibility remain deferred (`api.spl:555`). | Bounded scrollback and explicit supported interaction scope; prove retrieval beyond screen height and copy/paste. |
| P2 | CLI list/capture discard results (`smux_app.spl:58-60,91-92`); no interactive attach UI or multi-process client fanout is exposed there. | Print results and test real independent clients with visible output and input ownership. |

The proposed admission changes reject invalid sessions, sizes, empty client IDs,
and a fifth client, and allow rebinding. Split planning now validates direction
and minimum dimensions and reserves a separator cell. These improvements are
coherent by inspection; focused execution remains required. `h` divides rows
and `v` columns under the existing API convention: do not advertise these as
tmux command-line flag compatibility.

Existing controlling-terminal tests query unusual geometry **before spawn**
(`smux_pty_controlling_terminal_spec.spl:112-134`); they cannot certify live
resize. Multiple attachment records cannot certify simultaneous client screens.

The new `test/03_system/tools/smux_service_features_spec.spl` uses production
API calls with concrete geometry, ownership, focus and admission assertions.
The new `smux_windows_conpty_features_spec.spl` creates real shells and checks
tokens assembled by child variable expansion, rather than accepting literal
input echo. Its detached scenario keeps the hosting process alive and actively
polls capture: it does not establish undrained background operation or reconnect
from another process. These sources improve evidence design but remain
**TEST_BLOCKED / unexecuted** in this review. Manual generation and runtime
admission are separate outstanding gates.

## Independent source and manual review

Reviewed the final 15 service scenarios, three Windows scenarios, their two
manual mirrors under `doc/06_spec/03_system/tools/`, and
`doc/03_plan/sys_test/smux_windows_phase3_features.md`. Source/test design and
authored-manual quality are **ACCEPTED with TEST_BLOCKED**; this is not verify
PASS or generated-manual admission. No lower-model sidecar supplied findings.

The revised client test fills all four slots before rebinding, rejects a fifth
client, and detaches each survivor exactly once. The production split tests
assert concrete dimensions, conservation with a separator, refusal without
mutation, and independent session/window ownership. Child-output oracles
require variable-expanded markers absent from submitted input. Both manual
drafts accurately identify themselves as unexecuted expected workflows and
describe the independent-client, rendering, undrained-background and live-resize
exclusions. Polling is correctly documented as at most five seconds of sleeps
plus capture/runner work, not a hard wall-clock deadline. No P0/P1 defect was
found in this bounded source/manual batch. Runtime outcomes remain unknown.

## Persistent owner design extension

<!-- codex-architecture -->

**Proposed source architecture, not runtime acceptance.** The findings above
describe the initial audited baseline; subsequent owner/layout implementation
must be assessed separately. Root owns integration/final review; the layout
lane owns geometry; this lane owns independent design review. Lower-model
sidecars: N/A.

### Reuse and provider prerequisites

Prefer loopback TCP for the first transport. `std.nogc_sync_mut.io.tcp` already
exposes listener bind/accept timeout, stream connect/read/write, and finite
timeouts. `src/app/ui.cli/socket_server.spl:137-161` demonstrates independent
process access but serially blocks inside one client's read loop; copying that
loop would starve PTYs. `src/app/office/sheets/calc_access_session_host.spl:12`
demonstrates existing scalar socket facades for staged native consumers.

Named pipes are not a shorter implemented path:
`src/app/simple_process_manager/transport/spm_transport_host.spl:92-95` explicitly
refuses host listen; its Windows pathname still feeds a Unix-socket extern.
Do not infer a working named-pipe server from that module's description.

Native Windows qualification has another concrete blocker beyond PTYs:
`src/runtime/runtime_native.c:16484-16508` defines the core-C Windows TCP
operations as failure stubs. The Rust host implementation in
`src/compiler_rust/runtime/src/value/net_tcp.rs` is a different runtime lane;
`runtime_smf_socket_shims.c:7-18` explicitly distinguishes those ABI universes.
A successful link alone therefore cannot admit the Windows TCP owner. Verify
actual loopback traffic on the precise final artifact and implement missing
provider operations through the approved infrastructure boundary.

### Smallest owner and client split

Keep `os.apps.smux.api` as the sole mutable session/PTY owner. Add a finite
`smux_poll_output` operation that drains every admitted pane without requiring
capture or a client. A hosted owner entrypoint runs independently of stdin;
client EOF detaches only the client. Explicit authenticated `serve` and
`request` modes are a useful first increment: an independently started
foreground server survives request-client exit, but this does not establish
automatic daemon launch or survival of the server's own terminal closure.

Put framing/commands in a shared smux protocol module, network buffers and
deadlines in one transport module, and launch/platform details behind the
existing process facade. Avoid multiple copies of service state in clients.
Use one single-threaded owner so PTY/state mutations stay ordered; no worker
threads or shared mutable client state are required for the existing bounds.

Each iteration drains a bounded number of chunks per pane, accepts with a
finite timeout, processes bounded input from each pending connection, dispatches
complete requests, and advances bounded replies. Suggested initial bounds:
16 pending connections, 4096 request bytes, eight reads per pane per turn, and
one shared request/reply deadline. Check nonblocking configuration success;
close any descriptor that cannot satisfy the loop contract. Bind loopback only,
require a nonempty capability token, and refuse before mutation on auth failure.

Retain raw partial request bytes until a complete frame exists, then decode
UTF-8 once. Bound reply bytes separately from request size, preserve write
offsets, and close a slow client at its deadline. `TcpStream.read` maps all
provider failures, including would-block, to one error (`tcp.spl:217-232`), so
an error cannot be treated as immediate disconnect in this loop. Keep it
pending until deadline or expose typed `try_read`; empty successful reads mean
EOF. `write_text` performs one write and cannot resume a partial reply
(`:429-443`); `write_all` can monopolize the loop. Use counted byte writes and
retained offsets. Never use stateless `read_line` on nonblocking fragmented
requests.

One request/reply connection may close while its authenticated logical client
attachment remains. Each client process can independently poll capture and send
input. Add explicit attachment identity and detach semantics; do not interpret
every short-lived transport disconnect as session destruction. Shared focused
pane routing is an initial policy; client-specific view/focus and input-control
arbitration require an explicit subsequent contract.

### Windows launcher and lifecycle

`src/lib/nogc_sync_mut/io/windows_worker_launcher.spl:19,47-49,74` already
provides a pure-Simple launcher using `CreateProcessW`, `CREATE_NO_WINDOW`,
noninherited handles, and a detach operation that closes manager handles.
Reuse through a process-owner adapter if automatic startup is added. Its
absence of a newly created JobObject does not prove independence from an
inherited parent job: Windows job association and permitted breakaway must be
tested in the actual launching environment. See Microsoft's
[job documentation](https://learn.microsoft.com/en-us/windows/win32/procthread/job-objects)
and [creation flags](https://learn.microsoft.com/en-us/windows/win32/procthread/process-creation-flags),
fetched through context-mode for this review. Persistent operation means owner
survival across client exit; owner crash recovery and machine restart remain
separate requirements.

### Required real-process evidence

Start one admitted native owner and two distinct client processes. Launch a
child that produces more than pipe capacity and writes an independent completion
marker; terminate both clients and prove completion before reconnecting.
Reconnect a fresh client, verify the original child PID/state and capture, then
exercise concurrent separate requests. A slow partial request, nonreading reply
client, malformed/auth-failing request, and capacity refusal must not stop PTY
progress. Shut down the owner explicitly and confirm all PTYs/sockets are
released. Record binary hash, provenance, exit codes, timing, and transcripts.

### Named-layout model path

The original pure `mux_model.spl:98-109` always chooses even columns; its
`MuxWindow` has no layout field. Add a per-window layout name and
`mux_select_layout(session, window_id, name) -> (MuxSession, bool)`, with pure
rect functions for `even-horizontal` (columns), `even-vertical` (rows),
`main-horizontal` (main pane above others), `main-vertical` (main pane left of
others), and `tiled`. Preserve the model's existing separator-free geometry;
it is distinct from the service API's split separator convention.

Validate the full unzoomed layout, including positive dimensions, nonoverlap,
containment and all pane IDs, before committing selection. Refuse insufficient
space without mutation; the original `mux_even_columns` clamps widths to one
and can extend beyond a too-small viewport. Preserve layout on every window
reconstruction, keep IDs/PIDs/PTY handles/focus intact, and reapply it on resize.
Zoom presents one full viewport while retaining the selected unzoomed layout.
Test uneven dimensions, one/many panes, insufficient space, unknown names,
selection while zoomed, and resize/close/add behavior. Model geometry alone
still does not deliver child resize or connect layouts to the service renderer.

### Named-layout source review outcome

Reviewed the implemented `mux_rects.spl` and `mux_model.spl` changes, ten
`smux_named_layouts_spec.spl` scenarios, and their authored manual. The five
layout names, gapless tiling, viewport-fit refusal, retained layout through
window reconstruction, zoom-hidden validation, inactive-window isolation, and
row-aware composition are coherent by source inspection. The review identified
an unbounded title-summary regression that could wrap a terminal row; the
implementation now bounds the header with `mux_pad_to(header, s.cols)` and the
stacked-render scenario asserts every row's width with long pane titles.
Source and authored-manual design are accepted with **TEST_BLOCKED**; neither
the `.spl` scenarios nor a real terminal frame were executed by this reviewer.

## Hosted owner implementation review

The subsequent `server.spl` implementation now separates an explicitly started
foreground owner from disposable request clients. Reviewed the retained byte
request/reply buffers, write offsets, authentication-before-dispatch, loopback
endpoint restriction, connection/request/reply bounds, absolute client deadlines,
and exact-length `SMUX/1` reply decoder. Socket EOF releases that socket rather
than resetting the service; authenticated `stop-server` performs owner cleanup.
The loop invokes the new bounded `smux_poll_output` independently of capture.
No P0/P1 defect was found in this bounded socket state-machine inspection;
provider availability and behavior remain unqualified.

**Blocking provider limitation:** bounded read counts do not bound all owner
work. `src/compiler_rust/runtime/src/value/pty.rs:386-403` writes synchronously
to the Windows input pipe using `WriteFile` while holding the session registry
mutex. A child that stops consuming input can therefore stall an authenticated
send or a terminal query reply produced during drain, preventing all other
owner turns. Nonblocking or bounded PTY input with retained pending bytes is a
prerequisite for a fairness/unattended-liveness claim. Socket deadlines cannot
interrupt that synchronous provider call. The core-C Windows TCP failure stubs
and missing qualified PTY provider remain separate execution blockers.

The 37 protocol/codec scenarios and authored manual were reviewed and accepted
as source-level evidence design with **TEST_BLOCKED**. They use production
dispatchers, inspect actual service state, identify focused input routing by
the exact no-child pane ID, and test Unicode byte lengths and truncated/extra
reply bytes. They explicitly exclude actual sockets, fragmentation, deadlines,
independent processes and ConPTY execution. No network or runtime PASS follows
from these sources.

Two integration findings were sent to the owning lanes: CLI request mode must
return failure for command-level refusals, not only authentication/transport
errors; and failed split/spawn rollback should restore the previous selected
layout as well as pane dimensions. Their final resolution requires inspecting
the subsequent edits rather than assuming this initial review covered them.

### Service layout and final command-path review

Reviewed the later production service layout integration, seven direct-service
layout scenarios and their authored manual, plus the Windows scenario extension
that checks child-owned variables after layout selection. The service gathers
pane identities before committing grid dimensions and complete window metadata
once; focus and child owners remain in the same records. Explicit manual-plan
invalidation on split/close/arbitrary resize prevents stale named coordinates.
Refused operations preserve the existing plan. These sources and manuals are
accepted by inspection with **TEST_BLOCKED**.

The hosted command path now exposes `layout`, `rects`, and `screen` using this
actual service owner. The bounded compositor captures each pane once before
painting, and the model renderer was refined to one rectangle traversal per
output row. Nested captured row arrays are read, not mutated through aliases.
The CLI now uses the shared `smux_remote_reply_ok` success classifier, addressing
command refusals returning exit zero. Failed split/spawn now reselects the prior
named layout and canvas after removing the new pane and restoring dimensions.
This restores metadata/geometry; resizing a VT grid is not a general rollback
of screen content already clipped during the attempted split.

**P2 compositor finding sent to the merge owner:** `_composite_screen` currently
measures/truncates strings with text length rather than terminal display cells.
`vt_text` joins wide glyphs with empty continuation cells, so a CJK/emoji row
does not have the same string length as its occupied terminal columns. Adjacent
panes can be padded or clipped incorrectly. Reuse cell-aware VT rows/width
calculation and test wide/combining characters, or retain an explicit compositor
limitation and tracking issue. The 60000-cell remote canvas bound also does not
guarantee a Unicode reply fits the independent 65536-byte cap; oversized replies
correctly remain command errors. No source review here admits host rendering,
native build success, ConPTY resize, or full tmux parity.

## Final checkpoint source review

**Independent source/authored-manual acceptance: ACCEPTED with TEST_BLOCKED.**
This supersedes unresolved source-review notes above where a resolution is
explicitly stated here. It is not production verification PASS, compiler
admission, generated-manual acceptance, or evidence of successful execution.

The compositor P2 finding is **resolved in source** by `smux_capture_cells` and
`smux_composite_cells`: capture retains VT cell boundaries and wide-glyph
continuations, commits its drain/metric update once, and composition explicitly
writes modified rows back into the canvas. Orphan clipped wide halves are
blanked. Review also found that width classification must inspect a stored
cell's first scalar rather than its combined string; the final `vt_cell_width`
does so and returns zero for an empty cell. The protocol spec's five
VT-generated Unicode scenarios include CJK, emoji, clipping, combining marks,
and U+115F plus U+0301 at a width-range endpoint. Exact composite strings and
VT readback cell coordinates are meaningful source oracles. The full protocol
spec now contains 57 authored, unexecuted scenarios.

Reviewed the four external-process owner lifecycle scenarios and authored
manual. Each request starts a separate compiled client. A release-file handshake
ensures the child emits more than 1 MiB only after detach; the fixture sends no
owner request during the interval and waits for exact child-written completion
contents before reconnecting. Review fixed the create-before-write race by
polling contents rather than file existence alone. Child-variable expansion
prevents raw input echo from satisfying the output oracle. Cleanup precedes
assertions; forced termination cannot satisfy graceful shutdown. These are
credible executable designs, not executed lifecycle evidence.

### Compiler transfer-boundary repair

Reviewed `call_has_thread_transfer_boundary` in
`src/compiler/50.mir/_MirLoweringExpr/switch_operators_calls.spl`, the five
`pty_spawn_transfer_boundary_spec.spl` scenarios, their authored manual, and
the actual-import fixture under
`test/fixtures/compiler_entrypoint/pty_spawn_transfer_owner/`.

The exception applies only to a direct callable named `spawn` whose symbol's
resolved defining module canonicalizes exactly to `lib.sys.pty`. It uses the
existing declaration-owner canonicalizer, not the local alias or a suffix
match. Import registration records the defining module separately from its
local lookup name (`module_import_registration.spl:912-927`). Missing/unknown
owner results remain outside the exception. `spawn_actor` and other spawn
owners retain the previous explicit Thread `TransferOut` path; LLVM's
unsupported transfer-envelope rejection is unchanged. No new alias-based bypass
was found in this scoped change. Existing broader spelling-based classification
limitations are not repaired or certified by this exception.

The five scenarios exercise actual HIR-to-MIR call lowering and serialized
instructions, including physical/Windows owner spellings, aliases, actor/builtin
positive transfer controls, and lookalike owner rejection. Their synthetic HIR
setup does not prove the loader/import pipeline; the real aliased-import fixture
must compile and run with rebuilt producers. The fixture uses invalid arguments
to avoid launching a child, so even a future fixture PASS will not qualify
ConPTY behavior. No new P0/P1 defect was found in this bounded compiler review.

### Required remaining gates

- Rebuild and admit the intended pure-Simple Windows producers. Compile and run
  the actual-import fixture with each relevant producer; run the five MIR
  regression scenarios and preserve binary provenance, exit codes, assertion
  counts and stdout. A prepatch diagnostic compiler cannot verify this repair.
- Qualify real Windows TCP and PTY providers on the final smux executable.
  Core-C Windows TCP failure stubs and unqualified PTY linkage remain blockers.
  Synchronous PTY input can still stall the owner; bounded socket work alone
  cannot establish fairness against a nonreading child.
- Execute the authored service, protocol, layout, live-ConPTY and external-owner
  scenarios once with admitted tooling, retaining actual transcripts and binary
  identities. No source-only count is an executed-test count.
- Generate the mirrored manuals with zero stubs, run required maintenance and
  repository audit checks, and complete compiler/core/lib plus MCP/LSP runtime
  smoke gates required by `AGENTS.md` for compiler changes.
- Continue to report live child resize, interactive independent viewports,
  copy/scrollback/key-table parity and owner restart/discovery as incomplete
  until their implementation and corresponding runtime evidence exist.

This final review accepts the bounded source checkpoint for honest retention.
It does not change the overall **FAIL for full tmux parity / TEST_BLOCKED for
Windows qualification** result.
