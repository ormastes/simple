# CoreMux server adapter implementation plan — source only

Root publication note: this preserves the v2 planning snapshot. The user subsequently authorized interim Phase 2 feature execution without rebuilding Phase 2, and landing only after actual feature tests pass. Phase 3 qualification remains separate. Current Phase 2 rejects explicit library-mode selection; the full cache generator also fails execution. The six-attempt diagnostic series is capped pending an explicit exception. Source review and implementation may continue independently. L2 configured-launch composition is now being scoped; it is not implemented or runtime-qualified by this plan.

Observed base: `42690d6342b55c997efebb54a8508cc9921c0ae6`, clean at initial observation.
Date: 2026-10-26. Status: PLAN / NOT_RUN. Foundation v2 is reviewed and committed;
this is a separate adapter source cycle 1. Before RenameWindow implementation: no production edits or launches made
for this plan. The original execution worktree is not touched.

## Authority and admission

The existing `api._svc` remains the sole service registry. API publication is the
only configuration clock. No adapter clone of sessions/windows/panes, observation
hash, namespace prefix inference, or fallback endpoint is permitted. All legacy
mutations must enter the same publication and event seams.

An explicit `--serve-coremux CONFIG` provisions exactly one named owner at startup,
with an optional separate legacy listener in the same process/owner loop. Clients
use ExistingOnly against that explicitly provisioned owner. Refuse startup if an
already populated in-process service would be implicitly adopted. CONFIG is SDN,
read via generic Sosix file owner: namespace, loopback CoreMux address, auth token,
separate namespace-stop token, optional loopback legacy address/token, bounded
frame/connection budgets. Tokens never appear in readiness output or errors.

Store a checked entropy-backed owner incarnation, service epoch, configured
namespace, transport policy and startup support evidence. Committed WPL now exports the approved
`sosix_pty_configured_launch_probe_v1() -> bool`: once per owner startup, real tiny
ConPTY open/close/cleanup, generic fallback false. Store its result; discovery does
not repeat it. False prevents full admission. This is mechanism availability, not
native qualification or a promise that later resource acquisition cannot fail.

Full admission requires all 39 operations implemented plus selected owner support.
No partial lease is issued while any mandatory mechanism below is absent.
`NotRun` evidence remains truthful and permits initial qualification attempts;
`Qualified` is never fabricated. Invalid/unsupported input is refused before
reservation/effects. Failure after any real effect reports Partial/Unknown and
retains exact cleanup authority. No copied convenience facade is a provider.

## Complete 30-command implementation matrix

Every row needs typed dispatch, scoped owner-reference validation, ledger reserve
before effects, exact outcome receipt and checked snapshot projection. 'Exists'
below means source mechanism exists, never runtime PASS.

| # | Command | Existing source mechanism | Concrete remaining work | Lane |
|---|---|---|---|---|
| 1 | CreateSession | api.smux_create_session | Atomic name/size/capacity validation; configured first-child launch; checked failure compensation; background semantics | L2 |
| 2 | RenameSession | api.smux_rename_session | Typed ref/name dispatch and receipt | L4 |
| 3 | TerminateSession | api.smux_kill_session | Resumable checked teardown, exact partial cleanup receipt | L5 |
| 4 | StopOwnedNamespace | Legacy stop-server is transport-token only | Separate configured stop authority; checked all-child cleanup; reply drain before listener shutdown | L5 |
| 5 | CreateWindow | api.smux_new_window | Configured first-child launch and checked compensation; no empty-success window | L2 |
| 6 | RenameWindow | Source candidate smux_rename_window + rename_window_state | Owner implemented in this cycle; typed dispatch/receipt and runtime qualification still pending | L1/L4 |
| 7 | TerminateWindow | api.smux_kill_window | Resumable checked teardown and cleanup receipt | L5 |
| 8 | FocusWindow | api.smux_focus_window is session-global | Canonical client active-window context; scoped selected-client update and revision | L1 |
| 9 | LaunchPane | Existing API spawns into a reserved pane | Define deterministic new pane placement using existing split/layout owner, configured launch and exact rollback; do not overwrite existing child | L2 |
| 10 | SplitPane | api.smux_split_pane_sized + rollback | Configured launch in new pane; preserve opaque rollback and pending failed-close ownership | L2 |
| 11 | TerminatePane | api.smux_close_pane | Checked false means pending/failure, never removal success; receipt + surviving context update | L5/L1 |
| 12 | FocusPane | api.smux_focus_pane | Validate selected client ancestry/context; update canonical client context and existing zoom rules | L1 |
| 13 | ResizePane | api.smux_resize | Typed bounds/native preflight; committed resize owner checks content-counter exhaustion before effects; Result refusal/uncertain compensation must be preserved | L4 |
| 14 | ResizeWindow | api.smux_arrange_window | Typed dimensions and receipt, preserving hidden/zoom/base geometry | L4 |
| 15 | SelectLayout | api.smux_select_layout | Map all typed kinds; Manual must mean actual retained/current geometry, not unknown name fallback | L4 |
| 16 | ToggleZoom | api.smux_toggle_zoom | Exact existing toggle semantics; typed target membership | L4 |
| 17 | HidePane | api.smux_hide_pane | Typed membership + context reconciliation | L4/L1 |
| 18 | ShowPane | api.smux_show_pane | Typed membership + receipt | L4 |
| 19 | Rebalance | api.smux_rebalance_window | Typed window dispatch and checked geometry | L4 |
| 20 | SetPaneTitle | api.smux_set_pane_title | Literal title validation and receipt | L4 |
| 21 | SetPaneBorder | api.smux_set_pane_border | Typed dispatch and checked native geometry | L4 |
| 22 | SetPaneBorderStatus | api.smux_set_pane_border_status | Typed dispatch and checked native geometry | L4 |
| 23 | AttachClient | api.smux_attach_leased | Bind exact attachment generation to CoreMux lease; preserve stable slot/context; no unmanaged downgrade | L1/L4 |
| 24 | DetachClient | api.smux_detach_leased | Enforce lease ownership; clear context, notifications and cursor authority, preserve children | L1/L4 |
| 25 | SetClientViewport | api.smux_client_resize_leased | Exact attachment token mapping; no-op renewal must not tick configuration | L1/L4 |
| 26 | SendLiteral | api.smux_send_text accepts text | Exact arbitrary bytes through bounded queue and PTY byte-write owner; no UTF8 replacement or shell interpretation | L3 |
| 27 | SendKeys | Interactive key routing is not typed key encoder | Canonical named/function/scalar modifier bytes, with explicit bounds; same byte queue | L3 |
| 28 | Paste | api.smux_paste_text is text/bracketed-policy based | Exact supplied bytes/bracketed/append-enter flags; preserve atomic queue admission and partial write state | L3 |
| 29 | SubmitShellCommand | api.smux_send_command | Scoped literal command + exactly one submit sequence through existing owner; no host shell execution | L3/L4 |
| 30 | Notify | client_notifications + render ACK protocol | Kind/TTL/multi-recipient expansion, lease/generation-safe receipts and actual ACK-to-Rendered mapping; no synthetic render | L3 |

## Other nine operations (39 total)

| # | Operation | Existing source mechanism | Concrete remaining work | Lane |
|---|---|---|---|---|
| 31 | Connect | core_mux_owner_admit + full capability validator | Full installed capability table, bounded typed initial snapshot preflight before publishing lease; startup-probe admission | L4 |
| 32 | Snapshot | api.smux_owner_snapshot + presentation/layout projections | Pure scoped projection, independent hidden flag, graph-consistent optional refs, actual child state, no PTY drain | L4/L1 |
| 33 | ResolveTarget | session_targets only resolves sessions | Exact object IDs, names/indexes/context grammar; ambiguity refuses, no prefix namespace authority | L4 |
| 34 | Capture | committed CaptureCursorOwner/apply | Auth refs, actual record incarnation, persist cursor even Err; bound single-pane ingestion before capture, retention diagnostics | L4/L5 |
| 35 | CurrentContext | Canonical clients currently only session/size | Canonical active window/pane state + scoped read, no adapter shadow | L1/L4 |
| 36 | RequestStatus | core_mux_owner_status | Receipt-only wire route even revoked lease within fixed retention; never renewal or new execution | L4 |
| 37 | Capabilities | Common descriptor schema/validator | Actual complete table and configured startup proof; successful live maintenance heartbeat only | L4 |
| 38 | PollEvents | No common retained event owner yet | Publication-time event journal including legacy mutations, decoded-content notifications, ACK notifications; bounded cursors and reconciliation on overflow | L3/L5 |
| 39 | Disconnect | core_mux_owner_revoke + reserved ledger slot | Checked release of owned attachments/cursors, exact retained response replay, children survive, no lost receipt/authority | L4/L5 |

## Proposed ownership boundaries (root assigns before production edits)

L1 — canonical context/metadata (independent lane):
- Existing `contract.spl`, `service.spl`, `client_attachment_service.spl`,
  `session_lifecycle.spl`, `service_revision.spl` only after explicit owner handoff.
- New `client_context_service.spl`, `window_metadata_service.spl`.
- Authoritative attachment context lives in canonical attachment records, not the
  adapter; public client object identity incorporates attachment generation so a
  stale ref cannot address a rebound client with the same caller label.
- Legacy focus/close/hide/remove paths must update/reconcile that state at their
  publication boundary. Define whether background means detached current state
  or creation intent from accepted contract before adding a persisted field.
- Window rename keeps all geometry, presentation and child ownership intact.
- Return explicit-state transforms; API hook list delivered to merge owner.

L2 — configured launch composition (independent lane):
- New `pane_configured_launch_service.spl` and `core_mux_launch_service.spl`.
- Reuse PtyLaunchV1/Exec/Shell/Set/Remove exactly; preserve cwd/env/argv without
  dropping any fields. Generic Sosix only; no WPL/sys/provider owner edits.
- Return existing PanePidUpdate including cleanup_pending; can_attach before
  effects; failed close retains exact fd/incarnation. Never label reserved pane
  Running. Clarify LaunchPane default placement rather than silently pick a
  caller-visible layout policy.
- API publication hooks returned to API merge owner, not concurrent edits.

L3 — exact input and notification/event mechanisms (split if needed):
- Input: `input_queue.spl`, `pane_io_service.spl`, new `core_mux_input_service.spl`.
  Existing queue preserves text for pipe ABI; add explicit byte path for PTY,
  while refusing unsupported arbitrary-byte pipe transport before effects.
  Provider full admission targets configured PTY children; no silent pipe fallback.
- Notifications: `client_notifications.spl`, `notification_protocol.spl`,
  `notification_client.spl`; new `core_mux_events.spl` for bounded observation
  records, not session state. ACK needs exact recipient generation and TTL.
- Add events at API publication and content ingestion, not observer hashes.
  Configuration events advance only when publication changes configuration;
  content-only events never tick config. Saturation is explicit before effects.
- All touched owner paths require explicit handoff; capture author owns current
  pane I/O/content revision fixes, so no concurrent edits there.

L4 — my adapter/projection lane after interfaces freeze:
- New `core_mux_adapter.spl`, `core_mux_snapshot.spl`, `core_mux_targets.spl`,
  `core_mux_commands.spl`, `core_mux_queries.spl`, `core_mux_config.spl`.
- Existing `core_mux_owner.spl` only for bounded actual composition metadata;
  sole server-local adapter state contains leases/ledger/cursors/events/config,
  never another mutable ServiceState. Pass state/result explicitly each turn.
- Refuse cross-owner/generation/namespace refs; native object IDs never reused
  without service epoch invalidation. Canonical client generation is distinct.
- Snapshot Running requires actual retained child observation, not positive PID
  alone; exit code can be nil, but never invent command text/status/background.
- Pre-encode/validate result within reserved response bound; serialize canonical
  request meaning excluding transport auth/correlation for idempotency.

L5 — owner loop/CLI/API integration (single merge owner, me unless reassigned):
- Existing `server.spl`, `api.spl`, `src/app/hosted_apps/smux_client.spl`.
- New `core_mux_transport.spl`, `core_mux_dispatch_steps.spl`.
- API is 787 lines: extract existing pure/explicit-state wrappers mechanically
  before additional hooks. No second API registry. Concrete extraction manifest
  must be reviewed before editing; helpers <800, API stays <800.
- Explicit `--serve-coremux CONFIG`; separate CoreMux and optional legacy ports,
  shared owner loop. Never protocol sniffing, endpoint fallback or sidecar owner.
- Tests: new focused owner/projection/dispatch unit specs plus actual
  `smux_coremux_server_native_spec.spl`; mirrored manuals and source report.
  Existing foundation tests unchanged except required real API compatibility.

## Finite scheduling, resource and progress policy

Reuse existing nonblocking TcpStream ownership. Maximum 16 pending sockets shared
between listeners; at most one accept per listener and one 4096-byte read/write
per client per turn, rotated start index. Validate four-byte size before growing
body; absolute header/body/write deadlines never slide on trickled bytes. Cap
aggregate retained transport bytes before allocation; codec frame max is a
ceiling, not permission to allocate 16 maximum frames without a global budget.
Only one completed frame decode and one command microstep per loop turn.

Run clock/lease maintenance before transport work; keep legacy 1-second sweep and
live heartbeat opportunities. Poll output by bounded pane/byte work, not an
unbounded drain. Capture ingestion is one bounded step, then cursor projection;
`ingestion_sequence` is decoded delivered UTF8, not proof about withheld native
bytes. No output hash substitutes for the ingestion signal.

Multi-pane teardown/stop/launch compensation is resumable with explicit pending
work held by the sole owner; each step yields between actual child-owner calls.
A terminal receipt is published only after checked native completion. Socket
closure does not cancel/reexecute an already reserved operation. Long single
native calls and whole-frame decoding remain measurement gates: a transport
budget alone cannot prove heartbeat latency. Do not move _svc into a shared
worker, fake timeout preemption, or advertise N2 latency before real evidence.

Reuse ledger bounds: 4096 total IDs per lease including disconnect reserve,
8192 global entries, 128 MiB accounted ledger bytes, sixteen reserved control
slots/retained leases. Reserve transport response and event capacity separately
before irreversible effects. Never evict live ID bindings. On revoke retire
normal payload/full result bytes while retaining exact receipts; identical
Disconnect replay retains exact response. Fixed retention does not slide on
status. Busy/NotApplied is only a pre-effect refusal; missing bindings Unknown.

## Ordered integration and tests (all NOT_RUN)

1. Freeze L1/L2/L3 helper contracts; source-review each bounded independent lane.
2. Implement pure snapshot/target projection against actual canonical records.
3. Bind all commands/queries with exact receipt, cleanup and event semantics.
4. Admit only after every row is real; codec exchange validation before success.
5. Bind dual-listener loop and actual CLI entry; no helper-only pretend provider.
6. Author real process/ConPTY workflow: explicit server config -> connect ->
   create -> argv/cwd/env proof -> literal/NUL/multibyte/key/paste -> capture ->
   detach/disconnect -> reconnect -> observe same background PID -> checked kill.
7. Add slow/trickled frame vs legacy heartbeat, lost-reply exact replay, quota
   rollover, cross-lease receipt refusal, startup probe false, native partial
   cleanup, resize/zoom/hide/context and notification-render ACK controls.
8. Root coordinates genuine admitted Phase3 native SSpec and retained negative
   preflight. No execution permitted yet. Compiler/core/lib/MCP smokes, all
   consumer integration, real tmux provider and N2 24-hour runs remain mandatory.

## Decisions needed before broad implementation

- Assign L1/L2/L3 disjoint paths and API merge ownership; do not overlap capture
  pre-resize repair or WPL probe files.
- Confirm LaunchPane placement and background snapshot meaning from contract;
  these must be specified, not silently invented by the adapter.
- Set exact event/transport bounds and command-step interfaces with lane authors.
- Approve mechanical API extraction manifest after helpers are chosen.

## Current bounded implementation selection

Only RenameWindow is approved for this cycle. The 30 command / 39 operation
matrix above is complete; all other missing owner/adapter/route work remains
unimplemented. Configured launch probe is now committed, but it is not yet bound
into a real CoreMux server startup. Existing resize returns typed checked
geometry outcomes, which future dispatch must preserve rather than flatten.

RenameWindow uses a pure canonical window transform and one checked API publish.
It preserves window identity, session membership, active selection, geometry,
zoom, presentation, clients, panes and native child handles. Same-name requests
are configuration no-ops. Common request name validation is reused without
shell/token reinterpretation; typed names can contain spaces and Unicode.
The source contract is not advertised as a complete CoreMux provider capability
until the full 39-operation owner/route has actually been implemented.
