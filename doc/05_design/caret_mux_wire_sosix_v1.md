# CoreMux typed SDN and Sosix client v1

Accepted A/N2 continuation, 2026-10-25. Source correction cycle2. STATUS NOT_RUN.
This checkpoint implements a codec and real synchronous TCP client. The new server
route, production composition/Caret/IDE consumers, actual runtime execution and
both-backend qualification remain pending. The legacy interactive line protocol
is unchanged and incompatible with this framed route. Never probe/fallback to it.

## Owners and stable interface

The reviewed CoreMuxV1/D1 contract files are unchanged. Common `wire_*_v1.spl`
files own the versioned typed schema, byte/node/depth budgets and correlation.
`wire_values_01..06_v1` contain typed field codecs; `wire_budget_01..03_v1` count
nodes without constructing SDN. `wire_envelope_v1` is the safe public byte boundary.
Inner value constructors are implementation helpers, not transport entrypoints.

Applications import `std.sosix.mux` with explicit semantic library configuration.
The selected implementation lives at `src/lib/nogc_sync_mut/sosix/mux.spl` and
`mux/{config,admission,transport,client}_v1.spl`. No copied family facade, implicit
family-directory selection, new foreign ABI, global environment read, shell
interpolation or service registry is added. Existing strict SDN/encoding owners,
TcpStream and Sosix monotonic time supply the implementation boundaries.

MuxSosixConfigV1 has host:text, port:i64, auth_token:text,max_frame_bytes:i64.
This client admits only literal127.0.0.1, port1..65535, ASCII credential32..256 and
frame ceiling4096..4194304. It is explicit ExistingOnly Smux; no TLS/remote-host,
server startup, discovery, automatic backend or CreateOwned claim. The factory
mux_sosix_client_v1 validates config and acquires no resource. SosixMuxClientV1
implements all six frozen CoreMuxV1 methods without default success bodies.

## Framing and allocation bounds

Each exchange uses one ephemeral TCP connection, sends one request and receives
one response. Four big-endian octets precede a strict UTF8 SDN body. Partial writes
and reads use at most8192 bytes per operation, recomputing remaining time from one
monotonic start. Every acquired stream is closed on every Result path. A native
write attempt is conservatively submitted even if the write returns an error.
Post-submission timeout, malformed response or lost result is Unknown and requires
reconciliation; there is no automatic mutation replay.

Typed byte preflight accounts for hex expansion, array/tag separators and worst-case
text escaping before SDN/hex construction. Exact typed node preflight enforces the
same250000-node budget as the strict parser. The acyclic frozen typed schema reaches
at most13 levels including envelope, below the64-level parser ceiling. Large binary
payloads remain admitted up to1MiB when the configured frame permits; the node guard
does not replace the4MiB ceiling with an unrelated tiny global byte limit.

Reply allocation is bounded independently from request size by the original request
or valid negotiation. Capture max_bytes reserves2048 bytes for envelope/identity/
continuation plus2x raw-byte hex cost. Event max_bytes is the conservative encoded
result budget; it is not raw content length. Impossible requests fail explicitly;
no silent truncation or parser-recovery mode exists. Only typed capture continuation
may represent truncation. Unknown schema/tag/arity/primitive, invalid UTF8, trailing
syntax, wrong correlation and excess limits fail closed without echoing payloads.

## Correlation, authority and failed admission

The envelope correlation is per transport exchange; mutation request IDs remain
lease/incarnation scoped. Every success is checked against its exact call/result
kind, owner handle, request/operation/cursor and bounds. Wire validation does not
authenticate an endpoint or lease, certify reported process PIDs, or upgrade NotRun
capability evidence. The real server must authenticate operator credentials and
owner-issued lease/history and reject unavailable mandatory support before effects.

For connect, a correctly correlated structurally decoded reply is first checked
against the original namespace/backend and validated handle/lease terms. Eligible
issued authority is retained cleanup-only BEFORE elapsed-deadline or full semantic
admission can reject the reply. Late/over-request/incomplete-capability issuance
returns Unknown/PartialFailure, keeps normal calls disabled and blocks another
connect on that instance. Foreign/malformed candidates confer no cleanup authority;
submitted uncertainty is still retained as a reconnect blocker without pretending
a trustworthy handle was extracted.

Recovery uses a separate reply ceiling derived only from the validated original
request/configuration. A rejected advertised2048-byte budget cannot prevent explicit
disconnect/status requests. `recovery_handle()` exposes only a received handle for
that purpose. A new instance is required for a new lease; the old one remains for
reconciliation. No failed admission is relabeled NotApplied after possible issuance.
Peer-controlled error details are replaced with fixed text; secrets/content are not
included in local diagnostics.

## Leases and idle scheduling

The client retains the reviewed connection lease terms. Normal renewal uses request
start plus TTL, never response arrival plus TTL. It checks the prior local interval
again at completion and cannot revive an expired/revoked token. RequestStatus is
always receipt-only and never renews, including when the token is otherwise live.
Receipt reads and identical disconnect replay do not slide the retained interval.

`maintain_lease()` is a concrete convenience using the ordinary Capabilities query.
Generic compositions can do the same through CoreMuxV1 and advertised terms. A real
idle timer remains a composition responsibility; there is no hidden thread/scheduler
or claim that merely constructing this client keeps a lease alive. Server monotonic
time remains authoritative. No client wall time or local record grants authority.

## Scoped snapshot projection

Session snapshots contain that session subtree only. Window snapshots contain the
requested window and its required parent session; no sibling window/session leaks.
Clients belong to the requested scope. Hidden/exited filters remove excluded panes;
layout/restore rectangles omit those panes without reflow. Optional references to
objects outside the projection are nil. Returned client context references must
exist and agree through session/window/pane ancestry; the client self-reference,
when present, identifies that same client. Restore-layout rectangles belong to the
same window as their pane. Nil optional context members remain valid.

## Focused controls and pending execution

- 16 pure codec cases cover all30 commands/full result shapes, full64-bit IDs,
 binary/Unicode, malformed SDN, bounds/correlation, graph/scope and exact node
 accounting, including a byte-fitting high-node rejection and1MiB binary roundtrip.
- 9 client controls exercise real config/deadline/admission/recovery production
 helpers and early no-I/O refusal. Typed value fixtures are not fake providers.
- 3 real endpoint cases require the newly implemented framed server, private owned
 namespace/auth configuration, actual admitted echo child and independent guard.
 They exercise real PTY output, horizontal split, disconnect/reconnect background
 survival, literal+Enter input, authentication and unavailable transport semantics.

All28 cases are authored and NOT_RUN; zero executions/passes. Manuals are authored,
not native docgen evidence. Original D1/source contract tests remain separate.
Retain actual admitted compiler/runtime/source hashes, command, output, cases with
failures/blocked/unrun, resource bounds and terminal cleanup artifacts when execution
becomes available. No seed or Phase2 rebuild substitutes for that evidence.

Required next system work includes actual fragmented/late/truncated endpoint replies,
mutation uncertainty plus RequestStatus, clock expiry/no revival/non-sliding retention,
capacity eviction, independently verified no leaked processes/leases, Caret and IDE
composition, tmux provider and all shared callers. N2 remains24 real hours on each
backend with two namespaces, two sessions each, four panes and two clients per
namespace. This source checkpoint is not full feature completion or N2 qualification.

## Endpoint evidence correction cycle3

Production codec/client v2 source is unchanged. The endpoint spec uses the exact
std.sosix.process.sosix_process_exists seam for externally owned server/child PIDs,
not app process_is_alive (which may mean a local child token or platform HANDLE).
This checks provider-specific presence, not incarnation identity. PID reuse and
permission/provider behavior require independent owner-guard evidence; an absent
PID alone is never proof of complete lease/terminal/handle cleanup.

The real split scenario now requires a distinct second pane/PID, independent ready
capture and a pane-specific literal/Enter echo, while preserving the first child.
Both identities/PIDs must remain observable across reconnect. Every disconnect
receipt whose release is claimed must report cleanup.pending=false, including the
second client, cleanup client and authentication controls. Pending/unknown cleanup
remains failure and the external guard remains mandatory on all result paths.
Three endpoint cases and all28 checkpoint cases remain authored NOT_RUN, with zero
executions. This correction does not add provider or full-feature qualification.

## Frozen schema names and positional fields



### MuxBackendV1

- Smux
- Tmux

### MuxEndpointPolicyV1

- ExistingOnly
- CreateOwned

### MuxLimitsV1

max_sessions: i64, max_reply_bytes: i64

### MuxConnectV1

backend: MuxBackendV1, namespace: text, endpoint_policy: MuxEndpointPolicyV1, client_identity: text, limits: MuxLimitsV1

### MuxDeadlineV1

timeout_ms: i64

### MuxHandleV1

owner_id: text, owner_generation: u64, lease_id: text

### MuxObjectKindV1

- Session
- Window
- Pane
- Client

### MuxObjectRefV1

owner_id: text, owner_generation: u64, kind: MuxObjectKindV1, object_id: text

### MuxScopeV1

- Namespace
- Session(target: MuxObjectRefV1)
- Window(target: MuxObjectRefV1)

### MuxVisibilityV1

include_hidden: bool, include_exited: bool

### MuxContextV1

client: MuxObjectRefV1?, session: MuxObjectRefV1?, window: MuxObjectRefV1?, pane: MuxObjectRefV1?

### MuxCaptureRangeV1

- Screen
- AllHistory
- Lines(first: i64, last: i64)

### MuxCaptureV1

pane: MuxObjectRefV1, range: MuxCaptureRangeV1, join_wrapped: bool, styled: bool, max_bytes: i64, continuation: text?

### MuxQueryV1

- Snapshot(scope: MuxScopeV1, visibility: MuxVisibilityV1)
- ResolveTarget(target: text, kind: MuxObjectKindV1, context: MuxContextV1)
- Capture(request: MuxCaptureV1)
- CurrentContext(client: MuxObjectRefV1)
- RequestStatus(request_id: u64)
- Capabilities

### MuxLaunchModeV1

- Exec(executable: text, argv: [text])
- Shell(command: text)

### MuxEnvironmentChangeV1

- Set(name: text, value: text)
- Remove(name: text)

### MuxCellSizeV1

columns: i64, rows: i64

### MuxLaunchV1

mode: MuxLaunchModeV1, cwd: text?, environment: [MuxEnvironmentChangeV1], size: MuxCellSizeV1

### MuxCreateSessionV1

name: text, first_window_name: text, launch: MuxLaunchV1, background: bool

### MuxNamespaceStopV1

owner_id: text, owner_generation: u64, stop_token: text

### MuxCreateWindowV1

session: MuxObjectRefV1, name: text, launch: MuxLaunchV1

### MuxSplitDirectionV1

- Horizontal
- Vertical

### MuxSplitSizeV1

- Equal
- Cells(count: i64)
- Percent(percent: i64)

### MuxSplitPaneV1

pane: MuxObjectRefV1, direction: MuxSplitDirectionV1, size: MuxSplitSizeV1, launch: MuxLaunchV1

### MuxLayoutKindV1

- Manual
- Tiled
- EvenHorizontal
- EvenVertical
- MainHorizontal
- MainVertical

### MuxBorderV1

- Hidden
- Single
- Double

### MuxBorderStatusV1

- Hidden
- Top
- Bottom

### MuxAttachClientV1

session: MuxObjectRefV1, client_identity: text, viewport: MuxCellSizeV1

### MuxNamedKeyV1

- Enter
- Escape
- Tab
- Backspace
- Delete
- Up
- Down
- Left
- Right
- Home
- End
- PageUp
- PageDown

### MuxKeyV1

- Named(key: MuxNamedKeyV1)
- Function(number: i64)
- Scalar(codepoint: u32, control: bool, alt: bool, shift: bool)

### MuxPasteV1

bytes: [u8], bracketed: bool, append_enter: bool

### MuxRecipientV1

- Client(target: MuxObjectRefV1)
- Session(target: MuxObjectRefV1)
- Pane(target: MuxObjectRefV1)

### MuxMessageKindV1

- Info
- Warning
- Error

### MuxNotifyV1

recipient: MuxRecipientV1, kind: MuxMessageKindV1, literal_text: text, ttl_ms: i64

### MuxCommandV1

- CreateSession(spec: MuxCreateSessionV1)
- RenameSession(target: MuxObjectRefV1, name: text)
- TerminateSession(target: MuxObjectRefV1)
- StopOwnedNamespace(authorization: MuxNamespaceStopV1)
- CreateWindow(spec: MuxCreateWindowV1)
- RenameWindow(target: MuxObjectRefV1, name: text)
- TerminateWindow(target: MuxObjectRefV1)
- FocusWindow(client: MuxObjectRefV1, window: MuxObjectRefV1)
- LaunchPane(window: MuxObjectRefV1, launch: MuxLaunchV1)
- SplitPane(spec: MuxSplitPaneV1)
- TerminatePane(target: MuxObjectRefV1)
- FocusPane(client: MuxObjectRefV1, pane: MuxObjectRefV1)
- ResizePane(pane: MuxObjectRefV1, size: MuxCellSizeV1)
- ResizeWindow(window: MuxObjectRefV1, size: MuxCellSizeV1)
- SelectLayout(window: MuxObjectRefV1, layout: MuxLayoutKindV1)
- ToggleZoom(window: MuxObjectRefV1, pane: MuxObjectRefV1)
- HidePane(pane: MuxObjectRefV1)
- ShowPane(pane: MuxObjectRefV1)
- Rebalance(window: MuxObjectRefV1)
- SetPaneTitle(pane: MuxObjectRefV1, title: text)
- SetPaneBorder(pane: MuxObjectRefV1, border: MuxBorderV1)
- SetPaneBorderStatus(pane: MuxObjectRefV1, status: MuxBorderStatusV1)
- AttachClient(spec: MuxAttachClientV1)
- DetachClient(client: MuxObjectRefV1)
- SetClientViewport(client: MuxObjectRefV1, size: MuxCellSizeV1)
- SendLiteral(pane: MuxObjectRefV1, bytes: [u8])
- SendKeys(pane: MuxObjectRefV1, keys: [MuxKeyV1])
- Paste(pane: MuxObjectRefV1, paste: MuxPasteV1)
- SubmitShellCommand(pane: MuxObjectRefV1, command: text)
- Notify(message: MuxNotifyV1)

### MuxRequestV1

handle: MuxHandleV1, request_id: u64, deadline: MuxDeadlineV1, expected_revision: u64?, command: MuxCommandV1

### MuxEventLimitsV1

max_events: i64, max_bytes: i64

### MuxDisconnectRequestV1

handle: MuxHandleV1, request_id: u64, deadline: MuxDeadlineV1

### MuxWireCallV1

- Connect(options: MuxConnectV1, deadline: MuxDeadlineV1)
- Query(handle: MuxHandleV1, query: MuxQueryV1, deadline: MuxDeadlineV1)
- Execute(request: MuxRequestV1)
- PollEvents(handle: MuxHandleV1, cursor: u64, limits: MuxEventLimitsV1, deadline: MuxDeadlineV1)
- Disconnect(request: MuxDisconnectRequestV1)

### MuxSessionStateV1

identity: MuxObjectRefV1, name: text, current_window: MuxObjectRefV1?, background: bool

### MuxRectV1

x_cells: i64, y_cells: i64, width_cells: i64, height_cells: i64

### MuxPaneRectV1

pane: MuxObjectRefV1, rectangle: MuxRectV1

### MuxLayoutStateV1

kind: MuxLayoutKindV1, canvas: MuxCellSizeV1, rectangles: [MuxPaneRectV1]

### MuxWindowStateV1

identity: MuxObjectRefV1, session: MuxObjectRefV1, name: text, index: i64, active_pane: MuxObjectRefV1?, layout: MuxLayoutStateV1, zoomed_pane: MuxObjectRefV1?, restore_layout: MuxLayoutStateV1?

### MuxChildStateV1

- Running(pid: i64)
- Exited(pid: i64, exit_code: i64?, signal: text?)
- Unknown(last_pid: i64?, reason: text)

### MuxPaneStateV1

identity: MuxObjectRefV1, session: MuxObjectRefV1, window: MuxObjectRefV1, legacy_id: text, index: i64, child: MuxChildStateV1, title: text, current_command: text, rectangle: MuxRectV1, focused: bool, hidden: bool, border: MuxBorderV1, border_status: MuxBorderStatusV1, content_revision: u64

### MuxClientStateV1

identity: MuxObjectRefV1, context: MuxContextV1, viewport: MuxCellSizeV1, attached: bool

### MuxCoreLimitsV1

discovery: MuxLimitsV1, max_windows: i64, max_panes: i64, max_clients: i64, max_input_bytes: i64, max_capture_bytes: i64, max_events: i64, max_request_timeout_ms: i64

### MuxOperationV1

- Connect
- Snapshot
- ResolveTarget
- Capture
- CurrentContext
- RequestStatus
- Capabilities
- PollEvents
- Disconnect
- CreateSession
- RenameSession
- TerminateSession
- StopOwnedNamespace
- CreateWindow
- RenameWindow
- TerminateWindow
- FocusWindow
- LaunchPane
- SplitPane
- TerminatePane
- FocusPane
- ResizePane
- ResizeWindow
- SelectLayout
- ToggleZoom
- HidePane
- ShowPane
- Rebalance
- SetPaneTitle
- SetPaneBorder
- SetPaneBorderStatus
- AttachClient
- DetachClient
- SetClientViewport
- SendLiteral
- SendKeys
- Paste
- SubmitShellCommand
- Notify

### CapLevel

- native
- emulated
- unavailable

### MuxEvidenceV1

- NotRun
- Blocked(reason: text)
- Qualified(receipt: text)

### MuxOperationCapabilityV1

operation: MuxOperationV1, level: CapLevel, backend: MuxBackendV1, backend_version: text, owner_id: text, owner_generation: u64, limits: MuxCoreLimitsV1, constraints: [text], evidence: MuxEvidenceV1

### MuxSnapshotV1

backend: MuxBackendV1, namespace: text, handle: MuxHandleV1, revision: u64, sessions: [MuxSessionStateV1], windows: [MuxWindowStateV1], panes: [MuxPaneStateV1], clients: [MuxClientStateV1], limits: MuxCoreLimitsV1, capabilities: [MuxOperationCapabilityV1]

### MuxLeaseTermsV1

lifetime_ms: i64, renew_after_ms: i64, retained_receipt_ms: i64, max_retained_receipts: i64

### MuxConnectionV1

snapshot: MuxSnapshotV1, lease_terms: MuxLeaseTermsV1

### MuxIngestionV1

- NotPolled
- NoNewOutput
- Ingested

### MuxCapturedV1

pane: MuxObjectRefV1, observed_revision: u64, content_revision: u64, ingestion: MuxIngestionV1, bytes: [u8], byte_extent: i64, truncated: bool, continuation: text?

### MuxRequestKnowledgeV1

- Pending
- Retained
- Expired
- NotKnown

### MuxCommitStateV1

- NotApplied
- Applied
- Partial
- Unknown

### MuxErrorKindV1

- Unsupported
- InvalidRequest
- InvalidTarget
- PermissionDenied
- Unavailable
- StaleRevision
- Busy
- Timeout
- PartialFailure

### MuxRequestReceiptV1

handle: MuxHandleV1, request_id: u64, operation: MuxOperationV1?, knowledge: MuxRequestKnowledgeV1, commit_state: MuxCommitStateV1, prior_revision: u64?, observed_revision: u64?, affected: [MuxObjectRefV1], error_kind: MuxErrorKindV1?, detail: text, cleanup_pending: bool

### MuxQueryResultV1

- Snapshot(snapshot: MuxSnapshotV1)
- ResolvedTarget(target: MuxObjectRefV1)
- Captured(capture: MuxCapturedV1)
- Context(context: MuxContextV1)
- RequestReceipt(receipt: MuxRequestReceiptV1)
- Capabilities(capabilities: [MuxOperationCapabilityV1])

### MuxCleanupV1

pending: bool, remaining: [MuxObjectRefV1], detail: text

### MuxNotificationStateV1

- Queued
- Rendered(clients: [MuxObjectRefV1])
- Expired

### MuxNotificationReceiptV1

notification_id: text, state: MuxNotificationStateV1

### MuxMutationV1

receipt: MuxRequestReceiptV1, revision: u64, created: [MuxObjectRefV1], changed: [MuxObjectRefV1], snapshot: MuxSnapshotV1, cleanup: MuxCleanupV1, notification: MuxNotificationReceiptV1?

### MuxEventKindV1

- ObjectCreated(target: MuxObjectRefV1)
- ObjectChanged(target: MuxObjectRefV1)
- ObjectTerminated(target: MuxObjectRefV1)
- ChildExited(pane: MuxObjectRefV1, state: MuxChildStateV1)
- ContentAvailable(pane: MuxObjectRefV1, content_revision: u64)
- LayoutChanged(window: MuxObjectRefV1)
- Notification(notification: MuxNotificationReceiptV1)
- LeaseRevoked

### MuxEventV1

cursor: u64, causal_request_id: u64?, observed_revision: u64, kind: MuxEventKindV1

### MuxEventBatchV1

owner_id: text, owner_generation: u64, from_cursor: u64, to_cursor: u64, events: [MuxEventV1], reconciliation_required: bool

### MuxDisconnectV1

receipt: MuxRequestReceiptV1, already_disconnected: bool, released_clients: [MuxObjectRefV1], revision: u64, cleanup: MuxCleanupV1

### MuxWireResultV1

- Connection(connection: MuxConnectionV1)
- Query(result: MuxQueryResultV1)
- Mutation(mutation: MuxMutationV1)
- Events(events: MuxEventBatchV1)
- Disconnect(disconnect: MuxDisconnectV1)

### MuxErrorV1

kind: MuxErrorKindV1, detail: text, request_id: u64, commit_state: MuxCommitStateV1, observed_revision: u64?, affected: [MuxObjectRefV1], cleanup_pending: bool
