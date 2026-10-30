# CoreMux persistent server foundations — source candidate

Source cycle 2, **WARN / NOT_RUN**. Baseline shared-tree commit
`61e47484277f98437f1f5090c94fb343bf51b4bc`. This implements approved owner
foundations and existing presentation integration; it does not bind a listener,
implement the full CoreMux provider port or claim native qualification.

## One registry and publication clock

`api.spl` retains the sole `_svc` registry. Its publications pass through
`service_revision.spl`, which compares exact previous/next metadata at each
commit. This catches legacy session/layout/zoom A→B→A, child owner/incarnation
changes, presentation maps, client attachment generations, and cleanup intent.
It does not hash observations or count generic `commit=true` flags. Terminal
content, ingestion sequence, input progress, metrics and heartbeat deadlines are
excluded. Capture-owned content/ingestion fields remain in the existing pane
record; no second output owner was added.

The API preflights writable revision authority before new structural/native
launch/input effects. The final revision tick is reserved for retirement and
checked cleanup; it cannot wrap. API reset advances an epoch, so reused local
IDs cannot revive an old CoreMux owner. Clock metadata caches cleanup and
attachment identities only, never a second service registry or authority token.
Checked cleanup remains available after ordinary writes are refused.

Explicit-state attachment transforms moved to `client_attachment_service.spl`.
The API publishes their returned state and clears only actual replaced/expired
attachment notices. Existing leased/unmanaged signatures remain. A failed PTY
spawn with `cleanup_pending` retains its capture-owner record and installs the
exact pane cleanup intent before publication; false cleanup is never ignored
or changed to success by this API.

The already implemented title/border/status/hide/show/rebalance/sized-split
owners are now bound through checked API wrappers. `smux_window_rects` reports
actual child content viewports; base allocation/restore projections remain
separate owner helpers. Interactive selection/input checks independent hide
state as well as zoom. The hosted client recognizes only the two added exact
explicit-hidden refusals and its existing exact zoom/missing-window refusals.
Recovery validates a visible replacement frame without replaying discarded
input. Direct explicit send-to-hidden-pane remains supported.

## Explicit-state connection authority

`core_mux_owner.spl`, `core_mux_leases.spl`, and `core_mux_requests.spl` contain
only namespace/incarnation, leases, IDs, deadlines and receipts. They never
store `ServiceState` or create child handles. Server composition must supply
checked Sosix entropy/time and commit returned state. These pure constructors
and shape-valid records cannot admit an endpoint by themselves.

Admission accepts only exact configured Smux/ExistingOnly namespace identity,
and validates the full installed mandatory capability set before publishing a
lease. `NotRun` is valid prequalification evidence for real implemented
mechanisms; it is not converted into Qualified and does not require an
impossible already-qualified first test. Missing required mechanisms still
refuse. The future adapter must build/size the actual Connection snapshot before
committing admission. No reduced provider, development lease or fabricated
capability descriptors were added.

Leases use owner incarnation, generation and non-reused serial+nonce tokens.
Expiry cannot renew; retention begins at actual expiry/revocation and never
slides. Maintenance must be persisted even if the following request fails.
Status is receipt-only and never renews. Old epoch/revoked tokens cannot act on
current sessions; retained-token status or identical disconnect replay is the
only narrow exception. Native client detach/capture-cursor release must still be
performed by the forthcoming checked dispatcher; metadata retirement does not
pretend those effects occurred.

## Capacity and progress policy

Defaults are 4096 total IDs per lease including its disconnect ID, 8192 global
entries, 128 MiB accounted storage, four live/sixteen retained leases and sixteen
global control slots. Control slots are included in the global entry count;
128 KiB per slot is withheld from normal byte admission. Each entry charges
32 KiB conservative bounded receipt metadata plus exact retained request/result
buffers or its pending reply reservation. Request payload/reply ceilings are
1 MiB, with smaller 4 KiB request/64 KiB reply bounds for reserved disconnect.

Reservation precedes effects. Equal IDs compare exact canonical payload bytes;
no monotonic ID restriction, probabilistic identity hash, or live binding
eviction is used. The future codec adapter must exclude transport correlation
and authentication from canonical command identity while retaining semantic
request fields. Replays retain original deadline and never execute twice.
Completion cannot exceed its reserved response budget. Partial/Unknown
outcomes retain original typed receipt fields and cleanup status.

At a live lease's normal quota, Busy/NotApplied explicitly requests rollover;
disconnect capacity remains available. Disconnect/reconnect preserves background
sessions and starts a fresh lease scope. On revocation, completed normal payload/full
response buffers are released; pending request bytes survive until completion
or final retention expiry so a still-owned step does not lose its parameters.
Exact ID/operation/knowledge/commit/revisions/
affected/error/detail/cleanup receipts remain. Disconnect retains exact payload
and response for replay. Global pressure may require fixed retention expiry;
it never silently drops a live identity or re-executes an evicted request.
Lookup is bounded linear in at most 8192 entries; real latency/RSS under N2
remains unmeasured and required, not presumed from source ceilings.

## Scheduling boundary for the next integration stage

No codec/listener is bound by this change. The proposed shared owner loop must
service legacy lease heartbeat/expiry and CoreMux maintenance every iteration,
with bounded per-connection reads/writes and a global byte/work budget. A
trickled frame keeps its original absolute deadline. Parse only a complete,
length-admitted body and never block reading the rest of a connection. Complete
frames waiting for execution also need bounded queue capacity and original
deadlines; no request receives a fresh budget after waiting.

Long operations require resumable owner steps: reserve request/cleanup authority,
perform one bounded provider step, service heartbeat/output/expiry, then resume
only that same request. Do not move mutable PTY/service registries into an
unreviewed worker or assume a synchronous native call meets the heartbeat bound.
An unbounded provider step is a genuine integration/qualification blocker that
must be fixed at its owner. Actual socket fairness and dispatch latency remain
NOT_RUN.

## Owned files and verification limits

Eight production paths: API, interactive protocol/client, and the five new
revision/attachment/owner/lease/request helper modules. The focused SSpec and
manual are `smux_coremux_owner_spec.spl` / `.md` in the tools system-test trees.
Eighteen scenarios are authored, zero executed. Original execution worktree and
all capture/presentation/PTY/wire owners remain untouched by this lane.

No compiler, helper, watchdog, native test, product, server or commit was
launched. Independent source review, real SPipe/docgen/manual evidence,
configured launch/capture/presentation closure, full provider admission,
rollover composition, process-tree cleanup, both backends and all N2 runs remain
required. This is not a release or complete Caret/IDE integration claim.

## Cycle 2 review corrections

The immutable v1 freeze retains the original fifteen authored cases. The two
source-review findings are corrected in v2; three focused cases are added.

Existing attachment replacement preserves all active client slots in order.
Only the bounded four-slot local value is rebuilt; the API publishes its final
state once. Same-size leased renewal still updates its lease deadline but does
not advance configuration. Leased reattachment advances generation; unmanaged
identical reattachment does not. Real API two-client controls cover both paths,
actual dimension changes, and old-token refusal without displacing the peer.

Checked split rollback no longer uses the fresh-mutation writable preflight.
It must still locate the existing opaque checkpoint and pass all current
ownership, focus, presentation and native geometry validation. Split and spawn
preflights remain unchanged. Compensation can consume the reserved final tick;
publication saturates and invalidates authority rather than reusing revisions.
The new control obtains before/split/restored snapshots from the real API, then
passes those exact snapshots through the production clock at MAX−2 and MAX−1.
It does not claim to have driven the private global API counter to exhaustion,
and does not add a public authority-injection setter. Actual native resize,
failed compensation and exhausted-owner runtime execution remain NOT_RUN.

The API invokes `service_revision_rollback_allowed` before checkpoint restore.
That exact pure gate requires initialized positive revision/epoch, an existing
checkpoint and no closing owner; it permits reserved/exhausted cleanup authority.
The boundary control exercises this same gate at MAX−2, MAX−1 and saturated MAX,
and refuses missing-checkpoint/closing-owner requests. Accidentally applying the
fresh-mutation writable gate inside this cleanup seam fails those controls.
