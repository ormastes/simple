# Caret mux implementation contract v1

Selected A/N2; 2026-10-25. Concrete interface shape accepted by root review.
These are language-level contracts, not existing callable code. Implementation
and runtime qualification remain pending.
See architecture ../04_architecture/caret_mux_tui.md and the audited caller matrix.

## Records and enums

| Name | Required fields/variants |
|---|---|
| MuxBackendV1 | Smux, Tmux; no Auto |
| MuxConnectV1 | backend, namespace, endpoint policy ExistingOnly/CreateOwned, client identity, declared limits |
| MuxHandleV1 | owner_id:text, owner_generation:u64, lease_id:text (opaque owner-incarnation/client token) |
| MuxObjectRefV1 | owner_id, owner_generation, kind Session/Window/Pane/Client, object_id:text |
| MuxRequestV1 | client lease, request_id:u64, deadline, command; request ID scoped to lease/generation |
| MuxCapabilityV1 | operation, support level, backend/version, owner generation, limits, constraints, evidence NotRun/Blocked/Qualified(receipt reference) |
| MuxErrorV1 | kind, bounded detail, request_id, commit_state, optional observed_revision, affected refs, cleanup_pending |
| MuxSnapshotV1 | owner identity/generation, revision, sessions/windows/panes/clients, limits, capabilities; immutable |
| MuxPaneStateV1 | ref, parent window/session refs, legacy %ID and index, real child PID/state/exit status, title/current command, cell rect, focus/zoom/hidden state |
| MuxLaunchV1 | executable+argv OR explicit shell command, cwd, environment delta, initial cell size; never both launch modes |
| MuxCaptureV1 | target, screen/history range including AllHistory, join_wrapped, styled, max_bytes; result content, byte extent, truncation/continuation status |
| MuxMutationV1 | request receipt, revision, created/changed refs, actual state and cleanup status; no fabricated ID |
| MuxEventBatchV1 | owner generation, from/to cursor, bounded events, reconciliation_required; independent of command stdout |
| MuxTerminalLeaseV1 | parent MuxHandleV1, capability kind/version, capability_generation; references same owner |
| MuxProviderPortV1 | Common typed transport/dispatch interface; registered by app composition, bound to one backend/owner generation; no library dependency on smux app implementation |

Text byte lengths, Unicode scalar offsets and terminal cell coordinates are
distinct fields/units. Rectangles use nonnegative cell coordinates and positive
content dimensions; borders are separately described. All numeric inputs have
overflow-safe validation. Caller-presented references are untrusted until the
owner checks kind, generation, membership and client authority.

## Public facade and traits

Concrete facade names:

The implemented D1 abstraction is discovery-only: `MuxProviderPortV1.connect`
returns `MuxDiscoveryV1`, a metadata snapshot containing its actual owner handle.
It is an abstract provider contract, not an implementation of the future facade
below. The planned facade validates/registers that observation and returns the
handle to its caller. Its query surface is presently only Sessions/HasSession;
the broader command, capture, event and optional capability ports below remain
design obligations, not callable D1 implementations. Shape constructors and
validators never authenticate an owner or create a client lease.

- mux_connect_v1(options: MuxConnectV1) -> Result<MuxHandleV1, MuxErrorV1>.
- mux_disconnect_v1(handle) -> Result<MuxDisconnectV1, MuxErrorV1>; idempotent
  repeated disconnect for the same owned lease does not kill sessions.
- mux_query_v1(handle, query: MuxQueryV1) -> Result<MuxQueryResultV1, MuxErrorV1>.
- mux_execute_v1(handle, request: MuxRequestV1) -> Result<MuxMutationV1, MuxErrorV1>.
- mux_poll_events_v1(handle, cursor, limits) -> Result<MuxEventBatchV1, MuxErrorV1>.
- mux_acquire_terminal_layout_v1(handle, required_operations) and
  mux_acquire_terminal_presentation_v1(handle, required_operations)
  -> Result<MuxTerminalLeaseV1, MuxErrorV1>.

CoreMuxV1 trait has read-only fn backend/capabilities/query and mutating me
execute/poll_events/disconnect, using the same typed contracts. Facade dispatch
selects one provider lease from its registry; it does not store mutable session
copies in each trait wrapper. Optional trait methods are me apply_plan and
me present/route_input with separate release. No combined trait group is needed.
If one is later required, declare its union explicitly and acquire one owner.

Composition calls mux_register_provider_v1(port, owner_binding) to receive a
registry-bound provider token. Connect resolves an explicitly selected token;
the token is verified, not freely constructible authority. Remote smux transport
serializes common versioned SDN envelopes to the authenticated owner endpoint.
Server-side composition registers core_mux_adapter with the app-owned dispatcher.
The Sosix facade never imports that adapter or any os/apps module. Registration
is composition-only, not a public CLI authority escalation mechanism.

MuxQueryV1 variants: Snapshot(scope), ResolveTarget(text,context),
Capture(MuxCaptureV1), CurrentContext(client), RequestStatus(request_id),
Capabilities. MuxQueryResultV1 carries the corresponding Snapshot/ResolvedTarget/
Captured/Context/RequestReceipt/Capabilities result; capture is not smuggled into
snapshot state. Scope selects namespace/session/window and includes declared
exited/hidden visibility. ResolveTarget returns ambiguous/missing errors instead
of choosing a different object. Legacy adapter owns exact target grammar and
format projection, while service owns identity and membership checks.

The fn query receiver means the client reference is not replaced. Snapshot,
ResolveTarget, CurrentContext and Capabilities are non-draining metadata reads;
Capture may poll and ingest queued child bytes through the owner, advancing
content revision/capture counters. Captured includes observed owner revision,
content revision and ingestion status. It does not consume history or erase the
next client's capture. Metadata/configuration revision is distinct from output
content revision. No-mutation assertions must not use a capture that itself
drains output, and must distinguish autonomous child events from request effects.
Unsupported validation occurs before capture polling or any owner mutation.

MuxCommandV1 is a closed typed sum, grouped here for readability:

| Variants | Required semantics |
|---|---|
| CreateSession, RenameSession, TerminateSession, StopOwnedNamespace | Persistent owner lifecycle; explicit authorization; isolated cleanup |
| CreateWindow, RenameWindow, TerminateWindow, FocusWindow | Name/index identity, launch options, current-window context |
| LaunchPane, SplitPane, TerminatePane, FocusPane | Real process/PTY side effects, before/after geometry, stable ID; failure cannot publish a live fake pane |
| ResizePane, ResizeWindow, SelectLayout, ToggleZoom, HidePane, ShowPane, Rebalance | Required layouts including even-horizontal/main-vertical, window-wide zoom restore, child resize, surviving hidden process |
| SetPaneTitle, SetPaneBorder, SetPaneBorderStatus | Required Caret formatting/presentation persisted in owner state |
| AttachClient, DetachClient, SetClientViewport | Independent lifetime, explicit client view/focus and size policy |
| SendLiteral, SendKeys, Paste, SubmitShellCommand | Distinct typed payloads; bracketed paste is not a replacement for literal input; argv launch is not a shell command |
| Notify | Typed message kind/recipient, bounded sanitized presentation; visible delivery only after rendering proof |

Commands include target references and their operation-specific payload records.
No generic untyped text dictionary is a substitute for these variants. Enumerate
all cases in provider dispatch; Unsupported cannot be converted into success.
The smux geometry/notification owners retain their existing result contracts;
the adapter maps them without inventing atomicity or observed delivery.

## Request and provider algorithms

1. Connect verifies selected backend, endpoint namespace/ownership, server
   identity/generation and limits; acquires an existing server or creates only
   a named owner it can later clean up. Return capability/evidence observations.
2. Resolve target against one authoritative snapshot; validate ownership again
   when executing. Capture the request ID, affected refs and prior revision.
3. Validate syntax, bounds and provider support before native mutation. For a
   split, plan geometry and reserve capacity; on spawn failure restore the prior
   geometry through the existing rollback owner or expose a partial result.
4. Execute once. Record actual new IDs/exit status/revision and pending cleanup.
   A response timeout is Unknown unless completion evidence says otherwise.
5. Publish bounded events after committed state. A consumer gap requires a fresh
   Snapshot and cursor reconciliation; do not silently drop resize/exit events.
6. Disconnect releases client-held capacity/view constraints; background panes
   continue. StopOwnedNamespace terminates only that authority's resources and
   keeps pending teardown observable until its bounded cleanup completes.

For tmux, one in-flight command per control connection initially; a response
state machine accepts begin -> payload -> end/error with matching identifiers.
Notifications outside command blocks feed the event decoder. Preserve escape
decoding for raw pane output independently from line framing and UTF8 carry.
Malformed framing, oversize responses or connection EOF fail pending requests
with commit Unknown where appropriate, then require reconnect reconciliation.
Do not mix asynchronous pane bytes into legacy capture/list stdout.

Use the existing tmux/Sosix process invocation owner with argv-safe escaping for
control commands. No shell reparsing of user payload. A server-confirmed operation
can still race with external tmux mutations; snapshots report observed state and
no stronger revision/CAS guarantee than the provider can implement. Local request
sequence numbers are not native tmux transactional revisions.

## Optional methods

TerminalLayoutV1.apply_plan(lease, expected_revision, plan, commit_policy)
returns a MuxLayoutOutcomeV1 with resulting geometry and per-step commit/cleanup
evidence. plan contains a complete target-window cell map, focus and optional
layout naming; IDs must be unique, contained and valid. AtomicRequired is
Unsupported when the provider cannot guarantee all-or-none changes, before any
child mutation. Explicit OrderedObserved policy can return PartialFailure with
the applied prefix. Mandatory single operations remain on CoreMux regardless.

TerminalPresentationV1.present(lease, overlay) describes extra literal content,
cell bounds, scope, expiration and z-order in a declared supported subset.
route_input binds an explicit client/surface focus token and routing policy;
arbitrary widget trees or interception of unrelated child input are invalid.
Unsupported extra overlays never disable required title/border/Notify commands.
Normal Caret widgets remain in the pane's established shared UI renderer.

## Legacy adapter projection

The hosted smux entry preserves --serve/--request/--attach and routes recognized
tmux-style argv through smux_tmux_compat. Parse global -L before command options.
Never join argv and split on spaces. The same compatibility dispatcher must be
used by Caret's legacy paths, not just a standalone demonstration command.

Compile format tokens into a bounded AST supporting audited fields, literals
and nested conditional `#{?window_zoomed_flag,#{pane_active},0}`. Rendering uses
one MuxSnapshotV1. Bad format/target/command exits nonzero with bounded stderr.
list output, -P pane IDs, numeric display-message fields and capture bytes go
only to stdout, with the caller's newline contract. Preserve -S -, -S negative,
-J, -e, -l, -c, -d, -P and named-key semantics exactly. Keep all audited std.tmux
wrapper shell/format outputs during migration; tests must inspect actual parsing.

Native PID/%paneID/index are different values. Inherit TMUX_PANE-equivalent
legacy identity for workspace self-exclusion, scoped to namespace and server
generation. Map last-pane destruction, hidden panes and exited panes according
to the legacy command, not the old dashboard's reusable-slot shortcut.

## TUI state and evidence contracts

Existing Caret TUI shows backend+namespace, real pane/process state, selected
view, operation error and pending cleanup. A required operation unavailable is
a blocking compatibility error. Optional overlays/layout-plan controls are
disabled with the exact unsupported constraint; status does not imply failure
of ordinary pane-child UI. Existing semantic UI snapshots/captures, not a new
protocol, observe this. Separate TUI capture plan is owned by the system-test lane.

Shared spec helper names: caret_mux_setup, caret_mux_check_state,
caret_mux_require_native_owner, caret_mux_capture_evidence,
caret_mux_assert_no_mutation, caret_mux_cleanup_owned. Setup returns real owner
leases plus evidence identities, never a fake backend. No temporary helper may
pass silently; absent implementation fails or records NOT_RUN explicitly.
Manual steps: "Start two isolated workspaces", "Launch the agent panes",
"Send literal text and named keys", "Change layout and restore zoom",
"Reconnect without losing the children", "Inspect unsupported extras",
"Verify cleanup of owned resources". Advanced stress details may fold; primary
workflow and before/after typed evidence must remain visible.

N2 minimum topology follows the final requirement literally: two namespaces,
two sessions each, four panes and two clients per namespace (eight panes/four
clients total; distribute at least two panes per session). A stronger four panes
per session is permitted but must be reported explicitly. Run 24 actual hours
on each backend; no time scaling. Measure warm metadata latency and independent
settled child layout latency, bounded queues, RSS, handles and child cleanup.
All runtime/spec/docgen evidence remains NOT_RUN pending admitted Phase3/full CLI.
