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

## Native Windows provider source and ABI review (2026-10-16 follow-up)

The new `windows_tcp.spl` / `windows_tcp_abi.spl` and
`windows_pty_owner.spl` / `windows_pty_abi.spl` / `windows_pty_codec.spl`
are actual Simple implementations of the Windows boundaries, not success
stubs. This supersedes the earlier absence-of-provider finding only for a
native product explicitly composed with `src/providers/windows_native/lib`
before `src/lib`. The default interpreter facades remain separate. Neither
source presence nor resolver tests establish that the final executable selected,
linked or executed these providers. **Native qualification remains TEST_BLOCKED.**

Source inspection finds the Win64 ABI shapes consistent: four-byte COORD by
value, eight-byte HANDLE/SOCKET and pointer parameters, signed HRESULT return,
112-byte STARTUPINFOEXW, 32-byte OVERLAPPED with event at byte24, 144-byte job
extended limits, 48-byte job accounting, 408-byte WSADATA, 16-byte sockaddr_in
and 16-byte WSAPOLLFD. The pseudoconsole attribute receives the HPCON value,
matching Microsoft's example, rather than a pointer to a handle variable.
These are inspected layouts, not compiler ABI execution evidence.

The PTY design supplies synchronous pipe ends to ConPTY while retaining an
overlapped client write endpoint for the owner. Accepted pending input owns its
buffer and OVERLAPPED until GetOverlappedResult reports completion; CancelIoEx
alone does not authorize freeing that memory. Output uses an exclusive reader
and PeekNamedPipe before bounded reads. Close breaks the output channel before
ClosePseudoConsole and retains pending requests plus process/job handles until
completion and process-tree termination are observed. Microsoft documents both
the cancellation lifetime requirement and the final-output close deadlock;
these motivate the design, but finite close latency still requires a real
supervised experiment. See [CancelIoEx](https://learn.microsoft.com/en-us/windows/win32/api/ioapiset/nf-ioapiset-cancelioex)
and [creating a pseudoconsole session](https://learn.microsoft.com/en-us/windows/console/creating-a-pseudoconsole-session).

The TCP implementation tracks a Winsock startup reference per admitted socket,
retains partial line bytes, returns actual partial write counts and distinguishes
EOF's empty byte array from an unavailable read. Its poll flags and layout match
[WSAPoll](https://learn.microsoft.com/en-us/windows/win32/api/winsock2/nf-winsock2-wsapoll);
the documented readable-listener condition guarantees a subsequent accept will
not block. No speculative poll/accept race is asserted by this review.

### Findings sent to owners before native admission

- **P1, persistent-owner availability:** `windows_tcp.spl:89-94` bounds a
  nonreused lifetime slot list at100000, including already closed sockets.
  The one-connection-per-request server therefore becomes permanently
  unreachable after100000 accepted requests, about27.8 hours at one per second.
  Unauthenticated connection churn also consumes slots. Replace the lifetime
  allocation with bounded reusable slots carrying generation-tagged logical
  handles; retain a regression that old handles cannot close a recycled socket.
  Merely increasing the lifetime cap postpones the same failure.
- **P1, cleanup proof correctness:** the inspected PTY version ignored
  CloseHandle results for the child thread and source input/output pipe ends
  (`windows_pty_owner.spl:224,232-235`), and for output in its open-failure
  unwind (`:129`). Those failures could lose resource ownership while a later
  cleanup proof reported success. The owner was asked to retain failed handles
  or propagate release failure into the global cleanup result and per-handle
  proof. A failed source output close can also interfere with EOF observation.
  Later fixes must be recorded explicitly; these are not silently waived.

Bare array.push in the TCP provider is not a confirmed defect: native
`lower_unresolved_array_push` invokes mutating rt_array_push and method
writeback (`method_calls_literals.spl:1223-1239`). Socket inheritance was raised
as defense in depth; the reviewed smux PTY CreateProcess uses inheritHandles
false, and the general Windows process owner restricts inherited handles with
an explicit allowlist, so no smux socket inheritance leak is demonstrated.

### Required native evidence

Run the real TCP and PTY fixtures separately with each admitted phase2 and
phase3 producer and retain producer/executable hashes, selected source roots,
link inputs, exit codes and stdout. Use an external process watchdog: a timer
checked after WriteFile cannot detect a call that never returns. Required
oracles include partial writes and EOF, finite idle accept, stale handles after
slot reuse, actual child-observed resize, independent shell state, fragmented
UTF-8, input saturation against a nonreading child, pending-write cancellation,
job emptiness and cleanup proof. Then run the independent smux owner fixture
with the final native product to prove output draining during its no-request
interval. The authored fixtures and resolver scenarios are useful source
coverage; none has been executed by this reviewer. Interactive multi-client
viewports, copy/key-table parity and full tmux parity remain separate gaps.

### Source corrections reviewed after the findings

Both P1 findings above are **resolved by source inspection**, not by an
executed regression. TCP now uses at most4096 reusable live slots and encodes
`fd = generation * 4096 + slot`. Every operation validates the live slot and
generation; a successful close preserves the generation while releasing its
socket, and reuse increments it. The maximum generation2251799813685247 keeps
the largest encoded value within signed i64. Capacity is checked before socket
creation or accept, so closed slots recover admission capacity. The updated
native fixture checks three concurrent live sockets, stale-handle rejection
across reuse and128 real create/close cycles without registry growth. Socket
inheritance is now explicitly disabled during admission as well.

The PTY owner now retains failed CloseHandle and HeapFree values, including
thread, source pipe ends and temporary command/attribute allocations. A failed
post-spawn release aborts admission and enters cleanup. Unpublished open
failures with retained resources enter the same private quarantine. Release
does not mark closed until every handle, temporary allocation and arena is
released; failed output close prevents HPCON close. Global cleanup failure is
sticky and prevents successful cleanup certification. This addresses the
identified false-proof path without freeing pending I/O storage.

No additional demonstrated P0/P1 defect was found in this bounded provider
review. Remaining qualifications include the fixed100000 lifetime PTY-handle
limit, actual ABI and linker execution, supervised close latency, input queue
integration, and runtime failure-path coverage. Source/manual checkpoint
acceptance is conditional on retaining these explicit gates; it is **not a
Windows runtime PASS**.

## Final queue, history, resize and shutdown source review

This bounded follow-up reviewed current `api.spl`, `input_queue.spl`,
`window_layout_service.spl`, `server.spl`, `smux_remote.spl`, `vt_history.spl`,
the relevant `service.spl` projections and native provider overlays. The
requested shorthand `remote_cmds.spl` refers to `smux_remote.spl`; no new
parallel command implementation was assumed. No build was restarted and no
runtime result is claimed.

- **Input ownership:** `input_queue.spl:15-45` caps retained UTF-8 input at65536
  bytes, retains the original text for the piped-process byte-offset boundary,
  offers at most4096 bytes per flush and advances only by the provider's actual
  accepted count. A partial UTF-8 scalar is not replayed by slicing text at a
  byte offset. `_flush_input` (`api.spl:180`) waits for a prior provider-owned
  write before offering another chunk; errors are sticky. Terminal query
  replies use the same ordered queue and cannot create an unbounded secondary
  accumulator. `smux_send_text` returns acceptance, while input-status exposes
  pending, queued or idle. The owner tick drains up to eight chunks per pane
  and offers one queued write; real fairness still requires native execution.
- **Real resize:** split and direct resize call the capable PTY backend before
  committing service/VT geometry (`api.spl:390,446`). Named layout validates
  every rectangle before touching a child and resizes each existing PTY;
  failure attempts to restore previously changed children and explicitly
  reports incomplete rollback (`window_layout_service.spl:45-76`). The API
  commits the new named geometry only after that helper succeeds. This is
  source support for actual Windows ResizePseudoConsole, not evidence that a
  child observed it. Noncapable default providers retain their documented
  grid-only path; native overlay selection is therefore part of admission.
- **History:** retained primary-screen cell rows now exist with default2000
  and maximum10000 rows. Full-primary scrolling records displaced cells;
  alternate-screen activity, partial regions and line editing do not populate
  primary history. Frozen captures retain history and visible cells together.
  Capture bounds and session/window/pane ownership are checked before draining;
  the capture metric commits once (`api.spl:761`). The fallback to piped output
  is restricted to an actual piped child and excludes alternate or frozen
  empty frames (`service.spl:96`). This resolves the historical absence of a
  scrollback implementation at source level, without providing copy mode.
- **Shutdown:** server cleanup closes remaining sockets, releases service
  children and then polls provider quarantine with a two-second deadline
  (`server.spl:158-171`). Nonzero pending cleanup or any recorded socket close
  failure produces a nonzero server exit. The deadline begins after native
  close calls in reset: it bounds polling, not total shutdown wall-clock time.
  An external process-tree watchdog remains mandatory for native qualification.

No new demonstrated P0/P1 defect was found in these bounded paths. Two smaller
issues were sent to the root: split-spawn failure ignored errors from restoring
the original pane and named layout (`smux_remote.spl:212-215`), and the remote
send reply said "sent" while the API promised only acceptance (`:226`). The
first should disclose incomplete rollback; the second should use acceptance
wording or document the distinction. History line limits also do not override
the65536-byte response cap: large captures can fail framing admission. A line
count is not a guarantee that arbitrarily wide Unicode history fits a reply.

The two newly authored external-owner scenarios have meaningful source
oracles. WIN-006 requires actual capacity refusal after more than60000 accepted
bytes, keeps the blocked pane pending while a separate shell produces computed
output within five seconds, and cleans up before assertions. WIN-007 requires
computed old child lines to be absent from the real visible screen and present
in the actual history response. Neither substitutes input echo or a capture
mock for child output. The96-request saturation bound must be validated against
real ConPTY buffering. These are accepted authored scenarios, not executed
tests; their external180-second watchdog requirement remains in force.

### Major tmux gaps still retained

The original feature inventory above remains historical evidence. Later source
work narrows its gaps but does not turn it into an all-features PASS:

1. The independent foreground owner and disposable request clients provide a
   plausible persistent ownership path. Real detached output draining, child
   survival after a request client exits and reconnect from another process
   remain unqualified until the final native owner fixture runs. Automatic
   daemon launch, owner discovery and ordinary terminal lifecycle integration
   are not established by `--serve`/`--request` alone.
2. Attach records and captured composite screens do not implement a full
   interactive attached terminal. Continuous terminal input/rendering, client
   fanout, independent viewport sizing and multi-client input/resize policy
   remain major gaps. Remote window/pane commands exercise service operations;
   they do not demonstrate multiple live interactive screens.
3. Named layouts and child resizing now have implementations. General retained
   split-tree geometry, neighbor-aware interactive pane resizing and full
   layout behavior across arbitrary split/close operations remain narrower
   than tmux; manual edits intentionally invalidate a named plan.
4. Copy mode, selection and clipboard interaction, mouse support, key-table
   compatibility, tmux.conf and tmux control mode remain explicitly deferred
   (`api.spl:668-680`). Bounded history retrieval does not close these gaps.
5. Runtime correctness and NFR gates remain open: phase2/phase3 provider
   fixtures, final-product source-root/link identity, externally supervised
   cancellation and close, child-observed resize, detached draining, Unicode
   history, queue saturation/fairness, realistic throughput and maximum RSS.

**Result: source checkpoint accepted with the stated limitations;
TEST_BLOCKED for Windows runtime qualification and FAIL for full tmux parity.**

## Interactive client and native console source audit

The new hosted `--attach` route in `src/app/hosted_apps/smux_client.spl`
now reaches an actual interactive loop. It reads console input records,
forwards bounded input to an explicitly named window/pane, requests styled
frames, and supports local window/pane selection plus default prefix bindings.
Detach closes the local console lease and removes attachment metadata; it does
not issue stop-server. This supersedes the historical absence of interactive
client source. It remains uncompiled/unexecuted in this review.

`interactive_protocol.spl` validates session/window/pane ownership for explicit
targets. `frame_snapshot.spl` paints cells and SGR attributes from a single
service snapshot, with the selected client's cursor pane rather than changing
global focus. Synchronized updates freeze cursor position and visibility with
the cells and attributes. Cell text rejects C0/C1 controls; SGR accepts bounded
numeric/semicolon parameters, so arbitrary child escape sequences are not
replayed into the attached host console.

The console owner uses Win64 INPUT_RECORD size20 and KEY_EVENT payload offsets
4/8/10/14/16, and a22-byte CONSOLE_SCREEN_BUFFER_INFO with SMALL_RECT at10.
It duplicates the actual console handles without inheritance, snapshots both
modes before changing them, disables processed input so Ctrl-C becomes data,
and retains failed restoration/releases for retry. The codec carries UTF-16
surrogates and repeat counts between input records. Close attempts both mode
restorations even if alternate-screen exit fails. The two-second retry loops
still do not bound an individual native call.

Clipboard writes are explicit copy actions. The provider allocates movable
zeroed UTF-16 storage, unlocks before SetClipboardData, and never frees a handle
after successful ownership transfer. Failed native cleanup remains retained.
The native terminal overlay exports all seven capability operations; the
default provider refuses unsupported interaction. Actual user32 linkage in
the selected native product is still an admission gate.

### Interactive findings and reviewed corrections

1. **Copy-key batching:** the first controller compared an entire ordinary
   input chunk to one key, losing coalesced keys and fragmented arrows. The
   incremental `client_copy_input.spl` decoder now retains bounded CSI prefixes
   and emits ordered actions; the controller stops after copy/exit, and a
   lone Escape uses an explicit100ms deadline. This correction is accepted by
   source inspection only.
2. **P1 bottom-right scrolling:** output mode originally preserved immediate
   end-of-line wrapping. A full viewport paint could scroll the whole screen
   upon writing its final cell. The mode now includes
   DISABLE_NEWLINE_AUTO_RETURN (`saved | 13`) and still restores the exact saved
   mode. The native fixture writes a top-row guard, paints bottom-right, then
   reads the actual console cells to detect scrolling. The documented behavior
   is in [SetConsoleMode](https://learn.microsoft.com/en-us/windows/console/setconsolemode).
   Source correction accepted; this native oracle has not executed.
3. **P1 differing client dimensions:** local selections were independent, but
   each client's arrange request initially replaced shared geometry with its
   own dimensions and frames could overrun another client's viewport. Current
   `client-size` stores actual dimensions in authoritative attachment records;
   shared canvas uses the componentwise minimum for that session. Frame
   requests reflow after detach/size change. Clients reject frames larger than
   their local viewport and clear stale padding when the canvas or copy view
   changes. This is a defined shared-size policy, not independent per-client
   child geometries. Source correction accepted.
4. **P1 split/frame interleaving:** split temporarily invalidates a named layout
   before the initiating client sends its separate arrange request. A sibling
   frame at that point previously failed and detached the sibling. Reflow's
   equal-dimension fast path now also requires a known named layout; manual
   geometry is planned as tiled. The added production service/dispatch scenario
   exercises this exact interleaving without pretending to run two terminals.
   Source correction accepted.
5. **P1 dense history copy:** copy mode initially requested2000 lines
   unconditionally although the response limit is65536 bytes. Ordinary dense
   80-column history could therefore fail the reply and terminate attachment.
   A byte-bounded interactive history reply was requested; its final correction
   and tests require the follow-up recorded below before this finding closes.

The size-arbitration regression's resize_count assertion was also flagged:
named-layout selection did not increment that metric, so it could not prove
the absence of redundant backend resize calls. The inspected equal-size
fast path itself is correct; an uninformative counter assertion is not runtime
or call-count evidence.

### Remaining interaction and runtime limits

Basic copy mode, line-range selection and an explicit Unicode clipboard action
now have source implementations, replacing the former blanket copy-mode gap.
Full tmux key/config/control compatibility, mouse interaction, richer selection
semantics and application-specific terminal input modes remain narrower or
deferred. Abrupt client death leaves attachment metadata because no heartbeat
expiry exists; stale small dimensions can therefore constrain the shared canvas
until explicit detach/rebind. Automatic owner launch/discovery is still absent.

Native evidence must include two actual attached clients of different sizes in
one session, local window/pane input and cursor isolation, raw Ctrl-C reaching
the child, resize arbitration, split/frame interleaving, dense Unicode history
copy, bottom-right no-scroll behavior, and exact console restoration after
normal detach and recoverable failures. A fixture using two separate sessions
does not prove same-session geometry arbitration. All new runtime results,
selected overlay/link identities and realistic frame latency/RSS remain pending.

### Interactive source checkpoint after corrections

The dense-history P1 is now **resolved by source inspection**.
`client_history_reply.spl` budgets the complete reply prefix, encoded UTF-8 row
bytes and newline separators, retaining a contiguous suffix of newest whole
rows within65536 bytes. It examines at most2000 rows, encodes each inspected
row once and joins the retained suffix once. A newest row that cannot fit
produces a typed error instead of invalid UTF-8 or an empty successful copy.
The production `client-history` dispatch uses this helper; the public explicit
history command retains its existing semantics. Dense2000-row ASCII and
variable-width Unicode regressions assert exact retained suffixes and byte
bounds. These authored assertions have not run.

The uninformative resize_count assertion was removed from the size-arbitration
scenario. It now claims stable geometry only, with the manual explicitly
excluding instrumented native resize call-count evidence. The source fast path
and the manual-state sibling-frame regression remain independently reviewable.

All P1 findings identified in this interactive source pass have source fixes
reviewed above. No additional demonstrated P0/P1 was found in this bounded
review. Content-dependent frame/render byte budgets, stale attachment recovery,
full input-mode/key compatibility and the earlier runtime/NFR gates remain
limitations; this checkpoint does not expand them into claimed support.

**Interactive source checkpoint accepted for freeze. Native Windows execution,
two-client behavior and production readiness remain TEST_BLOCKED; full tmux
parity remains incomplete.**

## Stage 2 intrinsic-owner repair and shared-client fixture review

The observed bootstrap failure is a link boundary: the retained Stage 2 build
compiled1349 modules, then failed to resolve `__simple_pow` from MIR constant
folding. The compiler executable, its Hello compile/run and smux were not
admitted by that campaign. The root's detailed failure record is
[the Stage 2 power-owner bug](../08_tracking/bug/windows_stage2_pow_runtime_owner_missing_2026-10-16.md).

The reviewed repair in
`src/compiler_rust/compiler/src/pipeline/native_project/tools.rs:452-456`
adds the **existing** `runtime_core_intrinsics.c` to the seed runtime input
manifest; its implementation header is also included in the fingerprint inputs
at`:591`. The compile loop selects `.c` inputs, so the header is tracked as a
dependency rather than treated as another translation unit. Existing cache
admission checks both input fingerprint and exact archive membership, preventing
an old archive without the new owner from satisfying this repaired manifest.
The monolithic `runtime.c` is not added, avoiding duplicate ownership through
its inclusion of the same intrinsic implementation header.

This is a bootstrap runtime-composition correction, not a new Rust algorithm,
new C implementation, LLVM change or rewrite of the failing Simple expression.
The existing owner has the expected `int64_t (int64_t, int64_t)` C ABI.
`native_project/tests.rs:2812-2861` builds the actual core-C archive, checks the
normalized required symbol and counts exactly one definition in `nm -g
--defined-only` output. The regression is meaningful source coverage but was
not executed by this review. No demonstrated P0/P1 was found in the scoped
manifest/test repair; source acceptance does not certify the resulting archive.

The separate one-translation-unit compile and retained-object diagnostic
relink must keep original archives, object staging and canonical failure
receipts intact. A successful diagnostic link would prove that candidate's
missing-provider boundary was repaired. It would not admit the original
canonical Stage 2 build. Hello needs its own compiler invocation, emitted binary
identity, exit status and exact observed output; even a successful diagnostic
Hello would remain provisional until the repaired immutable bootstrap and
subsequent qualification gates run. No such runtime result is asserted here.

The new `windows_smux_shared_clients/main.spl` fixture was also reviewed at
source level. It launches two actual attached clients in the same session with
different ConPTY dimensions; resizing the real smaller terminal must be detected
by the actual client, without a fixture-issued client-size mutation. Computed
shell markers and explicit pane-history exclusions check local pane and window
input routing. A graceful smaller-client exit must release its size constraint
and let both windows grow. A real120-second child must be interrupted by raw
Ctrl-C before the retained shell produces a fresh computed marker within five
seconds. Client and owner exit statuses plus all three lease cleanup results
precede the PASS print.

These are useful independent-process oracles, unlike separate-session-only
coverage. Frame headers prove service geometry, not pixel-perfect rendering;
actual console cell, style, cursor and restoration evidence still belongs to
the native console/frame gates. Both producer builds, the external watchdog
receipt and all fixture execution remain pending. **Source checkpoint accepted;
runtime qualification remains TEST_BLOCKED.**

### Diagnostic intrinsic compilation: additional ownership gate

Subsequent diagnostic evidence narrows the manifest acceptance above. The
build owner compiled the existing standalone intrinsic translation unit in a
private directory with exit0, producing a3478-byte object. Its symbol listing
contains `__simple_pow`, but also a strong `__simple_intrinsic_bounds_check`.
The inspected archive-1/archive-2 collision listings show bounds-check
definitions in the other selected runtime archives. The stdio COMDAT overlap
is distinct from this intrinsic-owner overlap. A successful one-file compile
therefore does not establish valid final symbol ownership.

The frozen linker source already uses `/FORCE:MULTIPLE` for native-all plus
core-C supplementation (`native_project/linker.rs:2278-2304`), and explicitly
records that the intended precedence has lacked measured artifact evidence.
No new relaxation, and especially no unresolved-symbol allowance, is authorized
by this diagnostic. A faithful reconstructed link must preserve that existing
order and expose actual selected owners in a map or equivalent extraction
receipt for both power and bounds checking. Link exit0 alone cannot discharge
this requirement or certify the other overlapping runtime symbols.

The diagnostic command uses the GNU-style C flag branch for the pinned
clang-cl executable. This matches the frozen code: `is_msvc_compiler` in
`common/src/platform/cc_detect.rs:217` recognizes only cl/cl.exe, while the
separate atomics helper recognizes clang-cl. The original final linker argv
was not captured with verbose logging; the prospective diagnostic recipe is
**reconstructed from source and retained artifacts**, not a preserved original
argv. At this review boundary no diagnostic executable or Hello result existed.

The minimal manifest change remains a reasonable scoped source repair, but
runtime-composition acceptance is conditional on the additional owner evidence.
The original canonical Stage 2 failure remains unchanged and no new compiler
admission is inferred.

### Bounded reconstructed relink recipe review

The independently inspected diagnostic JSON and single-line response file have
the same255 arguments in the same order. All absolute inputs and the module
whole-archive input exist. The recipe retains the main/init objects,
native-all then core-C ordering,212 distinct module initialization roots,
three runtime retention roots and27 Windows libraries. It appends the private
intrinsic helper archive after the existing runtime archives. Executable and
map outputs stay in the private diagnostic directory.

The dry-run log selects LLVM23 lld-link for native MSVC. No unresolved-symbol
allowance, new stripping or additional duplicate-symbol relaxation was added;
the existing `/FORCE:MULTIPLE` and error-limit behavior are recorded explicitly.
This recipe was cleared for one diagnostic launch under a180-second process
Job watchdog. That clearance is not a link result, Hello result or canonical
compiler admission. Actual map/extraction evidence for power and bounds-check
ownership must precede interpreting any successful diagnostic executable.

### Remote repair and native source-root checkpoint (2026-10-17)

This is a bounded independent source review, not executable qualification.
The remote reference reviewed was `origin/release_phase3` at `e37c260fe5d`.
Remote `677b77f2907` already adds the existing
`runtime_core_intrinsics.c` owner to the Rust bootstrap runtime manifest,
addressing the missing `__simple_pow` translation unit observed in the frozen
1349-module failure. Remote `bcc977f537b` separately adds `f32_from_bits` and
`f64_from_bits` to the intrinsic implementation header. Neither change proves
the selected cross-archive bounds-check owner; the earlier native-all/Rust
archive collision finding and actual map requirement remain open.

Naively combining the local and remote manifest changes would select the same
translation unit twice. The isolated integration at
`D:/dev/simple-smux-upstream-20261017`, after `7a2fa6eee23`, was inspected:
`tools.rs:584` has one translation-unit entry and `tools.rs:600` retains the
local implementation-header fingerprint dependency. The actual archive ABI
regression must remain part of the integrated change. No frozen diagnostic
objects or original archives were modified by this review.

The integrated `switch_operators_calls.spl` diff against that remote reference
contains only the previously reviewed owner classifier and its call site.
At lines 6647–6660 it reads the resolved symbol's defining module and exempts
only canonical `lib.sys.pty` for `spawn`; local alias spelling does not choose
the exception. Other and unresolved `spawn` calls, and `spawn_actor`, retain
the existing transfer decision. The `TransferOut` emission remains at line
7182, and remote changes elsewhere in the lowering body remain intact.
This is source acceptance; the rebuilt compiler and real imported-PTY fixture
must still establish execution behavior.

The pending native SSpec source-root changes in the original feature checkout
were also reviewed. `native_compile_contract.spl:7` validates at most five
existing directories and rejects empty/control-bearing selectors; line 63
emits separate ordered `--source` arguments before the entry. The parser's
final normalization (`test_runner_args.spl:668`) selects LLVM when roots alone
are supplied and disables result/daemon reuse. The executor validates again
at `test_runner_execute.spl:1044`, includes root order in artifact selection,
and forwards the roots to the compiler at line 1127. Worker arguments preserve
the same order (`test_executor_parsing.spl:646`), and invocation receipts plus
metrics bind the length-framed root identity. Existing family parser facades
delegate to this canonical implementation. Root identity describes selectors;
it is not a claim that directory contents were cryptographically inventoried.

The ten `native_source_roots_spec.spl` scenarios use the production parser,
worker argument builder and compile contract, including invalid paths, the
five-root limit, explicit backend retention, order-sensitive receipts and
family delegates. The authored manual correctly labels execution/docgen
pending, and CLI help matches the implemented selection policy. No
demonstrated P0/P1 was found in this bounded source review. Remote
`3d6a3b7a0f6` changes the neighboring lifecycle cleanup return annotation,
not these root-selection files.

**Checkpoint: source/manual accepted; TEST_BLOCKED.** Required evidence remains
an admitted compiler executing the specs and native provider overlays, actual
selected-symbol/link ownership, compiler Hello, both producer fixture runs,
and the existing interactive/session/cleanup/performance gates. The earlier
full tmux gap inventory is unchanged; this checkpoint is not full parity or
runtime PASS.

### Actual diagnostic link artifact review (2026-10-17)

The newly executed private diagnostic link has an exit-zero receipt in
`root-link.exit.txt` and `root-link.job.env`. Independently inspected output
`simple-diagnostic.exe` is 22,857,216 bytes, SHA256
`BAD4C7FCED5D4C945A24A3DEB8F601685446A76DBE2ACE5938FEECCAEA1B04A9`.
These artifacts reside under the frozen checkout's private
`build/smux-windows-bootstrap/diagnostic-relink` directory.

The public map contains exactly one `__simple_pow` entry (line 31681), with
owner `intrinsics-helper:runtime_core_intrinsics.obj`. This establishes actual
selection of the added existing translation unit for this diagnostic link.
The map contains no public `__simple_intrinsic_bounds_check` entry. The stderr
warning at line 3093 reports duplicate definitions from native-all's cgu13
member and the helper object; it does not establish a surviving bounds-check
body. Dead stripping is a possible explanation, not a demonstrated result.
The duplicate ownership issue therefore remains open for canonical runtime
composition rather than being dismissed on successful linking.

The inspected recipe retains its existing `/FORCE:MULTIPLE` and has no
unresolved-symbol allowance. `root-link.environment.txt` explicitly labels
the selected MSVC/SDK paths as new diagnostic environment metadata, not the
uncaptured original environment. This is evidence of a successful diagnostic
link only. The original canonical build is still failed, and this review does
not supply compiler Hello, canonical admission, or smux runtime qualification.

### Diagnostic Hello transitive LLVM dependency (2026-10-17)

The diagnostic compiler's cold Hello build failed normally with exit 1 and
`quiescent=1`, not a timeout. Retained `root-hello-cold-build.stderr.log`
reports unresolved LLVM C API symbols, including `LLVMAddGlobal` and
`LLVMBuildIntToPtr`; the latter is referenced by the selected native-all
archive's Rust compiler cgu12 member. This is a new, concrete link dependency
failure, not a successful compiler Hello.

Source inspection confirms `native_all_support.spl:27` and line 31 select
backfill plus native-all for available core-C/auto runtime compositions.
Changing only the bundle flag therefore does not establish removal of the
transitive LLVM dependency. Native MSVC dependency selection is consumed in
`native_linking.spl:2497` and line 2643. A canonical fix should carry the
selected runtime archive's LLVM dependency through those link paths using
qualified toolchain authority, with missing-library diagnostics and actual
link/execution coverage. App source changes or dummy API definitions would
not repair this ownership contract.

One bounded diagnostic supplying the exact pinned LLVM-C import library via
the actual linker's `LINK` environment contract is accepted as a test of this
specific hypothesis. It must record the import-library hash, selected DLL/PATH
authority and newly supplied environment, preserve the failed attempt, and
retain ordinary unresolved-symbol errors. This approval is not a result and
does not replace a canonical source fix or admitted-producer rebuild.

### Discarded print-alias sections: concrete owner diagnosis (2026-10-17)

After adding the pinned LLVM import library, the next actual diagnostic Hello
link failed on `rt_value_print` and `rt_value_println` relocations into discarded
sections. The retained full stderr is
`C:/Users/ormas/AppData/Local/Temp/native-build-stderr-24252-1.log`; lines
3569–3573 identify references from native-all's Rust runtime cgu11 registry.
Earlier duplicate warnings at 3037–3063 identify the C runtime_native object
and Rust cgu10 definitions for `rt_print`, `rt_println`, `rt_print_value`, and
`rt_println_value`.

Read-only inspection of the actual native-all archive established the cause.
Its COFF symbol table places `rt_print` and `rt_value_print` at offset zero in
the same section 433; `rt_println` and `rt_value_println` share section 437.
Disassembly shows those sections are five-byte tail jumps with relocations to
`rt_print_value` and `rt_println_value`, respectively. Thus selecting the earlier
C definitions for the colliding short names discards the Rust sections that
also own otherwise unique word-order aliases. This is actual object evidence,
not an assumption about optimizer behavior.

Do not repair this by reversing archive precedence: C `rt_print(const char*)`
and Rust's `rt_print(RuntimeValue)` have different argument meaning. The narrow
compatible repair is for the selected C tagged printer owner to also expose
`rt_value_print(int64_t)` and `rt_value_println(int64_t)` as forwarding exports
to its existing `rt_print_value`/`rt_println_value`. That reproduces the exact
tail-call destinations present in the failing Rust object without changing
printing algorithms or raw-string symbol ownership. The current integrated
and reviewed remote sources do not contain these C aliases. Merely adding
`#[inline(never)]` to Rust wrappers is not accepted without optimized COFF proof
that the aliases survive in independent sections.

ABI evidence is deliberately scoped. Rust `RuntimeValue` is a transparent u64
(`value/core.rs:42`), and its tag mask, integer, heap, float, special, nil and
boolean encodings match the C tagged-word constants. This does not establish
universal heap interoperability: Rust `RuntimeString` includes a hash field
before its bytes, whereas C `RtCoreString` does not. The repair preserves the
already selected C canonical printer behavior; it does not resolve that
separate representation boundary.

A single diagnostic private object containing only the two forwarding exports,
injected with the pinned LLVM import library while preserving existing object
order and ordinary unresolved-symbol errors, is accepted to test this precise
repair. Record source/object hashes, exact injected order and selected ownership;
then execute the actual produced Hello. Canonical source ownership plus mixed
C/native-all link-and-call regressions remain required, including tagged nil,
booleans, integers, strings made by the selected C constructor, and independent
raw-pointer printing. A private shim link or source review alone supplies no
canonical admission or smux runtime PASS.

### Mixed-runtime Vulkan failure: diagnostic profile correction (2026-10-17)

The initial mixed-runtime print regression also failed on three Vulkan aliases.
Actual native-all COFF evidence places `rt_vulkan_device_count`,
`rt_vulkan_get_device`, `rt_vulkan_provider_device_count`, and
`rt_vulkan_selected_device_driver_identity_hash` in cgu06 section 335 with
leader `rt_get_host_target_code`. The mixed-link stderr at line 1537 reports
the C/Rust duplicate for that leader. This explains why selecting the C
definition strands the other Rust symbols; it does not imply their distinct
Vulkan operations can safely be aliased to one another.

The diagnostic compilation supplied `SIMPLE_CORE_C_STANDALONE=1` while linking
native-all. The C host-target definition already sits inside that guard
(`runtime_native.c:739–853`). The canonical runtime compiler explicitly omits
the standalone flag for native-all (`runtime_compiler.spl:809–814`). The
remote runtime_native diff from f612 contains container-probe fixes, not new
Vulkan provider definitions. Therefore no Vulkan source patch is warranted
from this experiment. Correcting the diagnostic compilation profile removes
the known duplicate owner; actual relink remains the deciding evidence.
Source confirms C/Rust host architecture code tables agree (0, 1, 2, -1).

### LLVM dependency patch: configured-input review finding (2026-10-17)

The new staging helper checks the producer's declared import-library path and
hash, copies and rechecks the bytes before the generation seal, and carries
the library plus receipt through tuple copies. Its pure selector correctly
rejects a foreign LLVM-C library when that library is in the inspected list.
These are source findings; shell test outcomes are owned by the implementation
lane and no Simple execution was performed by this reviewer.

**P1, reported to implementation owner:** the first wiring revision validated
object inputs and selected runtime archives but omitted already configured
MSVC libraries. `native_msvc_runtime_libraries` deduplicates by basename, so
an existing foreign `LLVM-C.lib` could suppress the qualified dependency even
while preflight validated the correct authority file. Both internal and
external MSVC paths must validate the combined actual configured/runtime
inputs before basename deduplication. The four pure selector cases alone do
not establish this call-site property. Source acceptance is withheld for
this finding pending the narrow correction and regression review.

### Print owner correction: scoped mixed-ABI evidence accepted (2026-10-17)

The corrected native-all compile profile produced a successful mixed C/Rust
link and execution. Independently inspected
`tagged-print-native-all-link.job.env` and `tagged-print-native-all-run.job.env`
both record complete, exit 0, quiescent 1. The retained stdout exactly matches
`tagged_print_word_order_alias_regression.expected.stdout` after CRLF
normalization, and run stderr is zero bytes. No test was rerun by this reviewer.

The map assigns all six names (`rt_print`, `rt_println`, `rt_print_value`,
`rt_println_value`, `rt_value_print`, `rt_value_println`) to
`native-all-subset-runtime_native.obj`. The fixture actually calls raw-pointer
printers separately, and word-order tagged printers with nil, positive and
negative integers, both booleans and C-constructor strings. The source patch
only forwards the two new aliases to the existing C tagged printers.

This closes the print-alias P1 for the reviewed source and demonstrated mixed
ABI composition. It also resolves the Vulkan diagnostic investigation without
a Vulkan source change: the corrected native-all compilation excludes the
standalone C section leader. This evidence does not establish Rust-allocated
heap interchange, canonical rebuilt-producer admission or smux qualification.
The independently reported configured LLVM-library bypass remains open until
its implementation correction is reviewed.

### LLVM configured-input correction and IO export review (2026-10-17)

The configured LLVM-library P1 is resolved in the reviewed source revision.
`native_all_msvc_llvm_link_inputs` combines configured libraries, object inputs
and selected runtime inputs before invoking the exact-authority validator.
The external MSVC call at `native_linking.spl:2670` performs this validation
before basename deduplication, and the internal COFF call at line 2519 includes
resolved configured library files. The fifth selector scenario uses this actual
combined planner to reject foreign and bare configured LLVM libraries when
native-all arrives through runtime or object inputs, and checks the valid
ordered result. No further demonstrated P0/P1 was found in this bounded
correction review. Simple compilation/execution remains pending; already
reported shell custody checks were not rerun.

The separate IO facade correction is also accepted by source inspection.
`io.spl` directly exports `rt_debug_set_active` from its concrete `debug_stubs`
owner and removes that name from the problematic self-reexport list. The added
`ds_is_active` reads the actual state mutated by `ds_set_active`. The native
fixture imports exactly the same `lib.nogc_sync_mut.io.debug_state` owner used
by debug_stubs and checks false, true, false transitions with distinct failure
codes before producing its expected output. This is a meaningful state oracle,
not a successful-void-call assertion.

The IO bug report correctly distinguishes the implementation lane's observed
76/76 HIR completion from its bounded timeout before native execution. This
review accepts the source and fixture for the scoped change; it does not
convert HIR clearance into a runtime state-transition or smux PASS.
