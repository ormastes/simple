# CoreMux consumer migration execution map - 2026-10-26

Status: **PLAN / NOT_RUN**. Source checkpoint `9cb95a1552b289d6e804333c5e79a807dc3beeb6` in `D:/dev/simple-coremux-shared-20261025`. Accepted scope remains A/N2 and REQ-CMUX-001..012 / NFR-CMUX-001..009, including the entire Caret suite, IDE and every actual shared-pane consumer. This plan authorizes no production edit or run. Root assigns source ownership and finite attempt budget before implementation. Merge owner: root; independent contract/source review: an agent other than the implementation owner; runtime evidence review must also inspect actual failures and cleanup.

## Evidence and current interfaces

This bounded update reuses `doc/09_report/shared_mux_application_inventory_2026-10-25.md` (A01-A10 and its 84 exact source hits). All 84 catalog paths still exist; no new full-tree scan was performed. Scoped reads checked consumer owners and frozen contract/SDK. Label/model hits remain distinct from actual callers. Runtime plugin/computed adapter discoveries must extend this manifest before application closure, never be silently excluded.

Canonical port: `src/lib/common/contracts/mux/port_v1.spl::CoreMuxV1`: fn backend; me connect/query/execute/poll_events/disconnect. Command/request records are in execution_v1; snapshots, capture, events, receipts and lease terms in observation_v1. All 30 command variants / 39 operation capabilities remain mandatory for full provider admission. Per-consumer command lists below identify migration call sites, not permission to optionalize other commands. Common query set: Snapshot (explicit scope/visibility), ResolveTarget, Capture (bounded continuation), CurrentContext, RequestStatus, Capabilities; polling, connection and disconnect apply to all real clients.

Application SDK import is `std.sosix.mux`; current implementation lives in `src/lib/nogc_sync_mut/sosix/mux{.spl,/config_v1.spl,/client_v1.spl,/transport_v1.spl,/admission_v1.spl}`. `MuxSosixConfigV1(host, port, auth_token, max_frame_bytes)` is explicit loopback endpoint configuration; `mux_sosix_client_v1` constructs a transport, not a server. The present client accepts only Smux + ExistingOnly. It does not implement Tmux, CreateOwned discovery, or server startup. New length-framed SDN wire is incompatible with the legacy line route; server composition must register its authenticated endpoint explicitly. Do not bind applications to merely source-reviewed foundations as though all commands were admitted.

## Shared migration rules and prerequisites

1. Composition chooses backend and namespace explicitly, injects one mutable provider instance, and retains its issued handle/incarnation/lease terms. Public shape-valid records do not mint authority. Never copy a controller/ServiceState into a client or infer NoGC from directory names. Broad roots plus semantic `--library-mode nogc-sync-mut` select the current SDK; an older producer must first prove flag capability. Other supported modes require genuine selected owners and positive value tests, not a forwarding directory workaround.
2. Host owner must provision/authenticate ExistingOnly endpoints and separately own any authorized namespace startup/stop. Current SDK's absent CreateOwned route is an owner prerequisite; application-owned silent spawn or port/token guessing is forbidden. A separate real Tmux CoreMux provider/composition is still required; direct std.tmux calls are not that implementation.
3. Normal query/poll renew only a live lease; composition needs a real idle timer at advertised cadence (concrete maintain_lease convenience or Capabilities query). Expired tokens never revive. Receipt-only RequestStatus/identical disconnect replay is confined to original owner/token/request binding and bounded non-sliding retention. Timeout after submission is Unknown; no automatic replay of mutation. Retain cleanup authority on rejected issued connections.
4. Missing mandatory capability blocks usable admission with typed Unsupported and no effect. Optional stronger TerminalLayoutV1 complete-plan and TerminalPresentationV1 overlays remain separately acquired, owner-bound leases: absent support disables only extras with visible status, and must leave metadata/config revision unchanged. Title/border/hide/show/rebalance/zoom and Notify are mandatory CoreMux, never hidden behind optional extensions. Acquisition names in design are proposals until concrete ports exist; no new fake default trait. For failure comparisons, Capture can ingest output: compare configuration revision/causal receipts and independently account for child output.
5. Preserve legacy argv/format contracts in `doc/09_report/caret_smux_compatibility_2026-10-25.md`; keep literal bytes, named keys, bracketed Paste, explicit shell command and notification distinct. Tmux may partially mutate before native error; Partial/Unknown receipts must stay honest. ToggleZoom restores any already zoomed window rather than switching target; pure same-active focus must preserve zoom. Unicode tests distinguish UTF8 bytes, scalars and display cells. Clipboard is positive operator action, never an automatic destructive fixture step.
6. Current owner boundaries: Sosix/server lane owns common validation rename, Smux API and new metadata helper; resize documentation belongs to final-review lane. This map edits neither. Caret, IDE, web/LLM, workspace, configured-family/Tmux and shell compositions need explicit root assignments after provider interfaces freeze.

## Consumer-specific migration and real SYSTEM cases

Every case below is **planned, not newly authored or executed**. Existing paths are reuse anchors, and absent paths are reservations only. Do not add wrapper-only tests or empty placeholders. Modern cases use `step("...")`, `caret_mux_setup` and `caret_mux_check_state` where shared helpers are useful; observations must reach actual processes/terminals/apps. Source/model-only assertions retain their narrower status.

### A01 - Caret cs dashboard

Existing paths:

- `src/app/llm_caret/pane_backend.spl`
- `src/app/llm_caret/cs_dashboard.spl`
- `src/app/llm_caret/cs_main.spl`

Current contract: Direct os.apps.smux.api or actual tmux process. _use_tmux requires both CS_PANE_BACKEND=tmux and successful probe, otherwise silently selects Smux; Windows probe refuses Tmux.

Owner prerequisite: Caret dashboard owner: inject one request-owned CoreMux provider; remove fallback; preserve legacy pane IDs/formats only at compatibility edge; owner-issued refs and persistent children replace local scope assumptions.

Required command mapping: `CreateSession`, `LaunchPane`, `SplitPane`, `FocusPane`, `ResizePane`, `SelectLayout`, `ToggleZoom`, `HidePane`, `ShowPane`, `Rebalance`, `SetPaneTitle`, `SetPaneBorder`, `SetPaneBorderStatus`, `SendLiteral`, `SendKeys`, `Paste`, `SubmitShellCommand`, `Notify`, `AttachClient`, `DetachClient`, `TerminatePane`. Common queries/lease/recovery apply.

Optional extension handling: GUI/TUI may acquire stronger layout/overlay leases after core admission; missing extras leave the ordinary child UI usable and visibly disabled. Mandatory-operation refusal blocks this consumer workflow; it is never a successful no-op.

Acceptance anchors:

- `test/03_system/app/llm_caret/caret_suite_tmux_window_system_spec.spl` (existing; inspect its actual evidence boundary before reuse).
- `test/03_system/app/llm_caret/feature/caret_mux_tui_spec.spl` (reserved; no spec/fixture implied).

- **A01-S1 / NOT_RUN:** Launch actual dashboard with explicit backend; child reports exact argv/cwd/env and independent readiness. Unavailable selected backend fails without creating the other backend.
- **A01-S2 / NOT_RUN:** Drive nested split, focus, hide/show, title/border, resize, rebalance and zoom/restore through real UI; assert child dimensions and stable pane IDs from independent owner observations.
- **A01-S3 / NOT_RUN:** Send literal metacharacters, keys, paste and notification through distinct paths; require actual rendering before notification ACK; detach/reopen dashboard retains background children, then authorized cleanup completes.

### A02 - Caret workspace CLI

Existing paths:

- `src/app/llm_caret/agent_workspace.spl`
- `src/app/llm_caret/workspace_cli.spl`

Current contract: Actual tmux/git process facade with private -L caret workspace socket, recursion-depth guard and TMUX_PANE self-exclusion; not CoreMux.

Owner prerequisite: Workspace owner: retain git worktree ownership/depth guard separately; map private socket to explicit namespace endpoint authority; resolve actual sender context for broadcast; do not turn git/worktree cleanup into server-global kill.

Required command mapping: `CreateSession`, `RenameSession`, `CreateWindow`, `RenameWindow`, `LaunchPane`, `AttachClient`, `DetachClient`, `SendLiteral`, `SendKeys`, `SubmitShellCommand`, `Notify`, `TerminateWindow`, `TerminateSession`, `StopOwnedNamespace`. Common queries/lease/recovery apply.

Optional extension handling: No optional extension is necessary for this baseline; any added extension must use separate acquisition and refusal assertions. Mandatory-operation refusal blocks this consumer workflow; it is never a successful no-op.

Acceptance anchors:

- `test/03_system/app/llm_caret/workspace_cli_system_spec.spl` (existing; inspect its actual evidence boundary before reuse).
- `test/03_system/app/llm_caret/workspace_recovery_system_spec.spl` (existing; inspect its actual evidence boundary before reuse).
- `test/03_system/app/llm_caret/agent_team_workspace_system_spec.spl` (existing; inspect its actual evidence boundary before reuse).

- **A02-S1 / NOT_RUN:** Run real workspace CLI in two namespaces; create/discover/rename independent sessions/windows; duplicate and ambiguous target errors affect neither neighbor.
- **A02-S2 / NOT_RUN:** Launch two real agent children and broadcast from a third client with sender exclusion; verify only addressed child output and bounded captures.
- **A02-S3 / NOT_RUN:** Crash/reconnect CLI while background children continue; stale-generation refs fail; teardown only authorized namespace/worktrees and retain exact cleanup receipt.

### A03 - Caret workbench GUI/TUI

Existing paths:

- `src/app/llm_caret/workbench/pane_team.spl`
- `src/app/llm_caret/workbench/pane_source.spl`
- `src/app/llm_caret/workbench/session_source.spl`
- `src/app/llm_caret/workbench/session_contract.spl`
- `src/app/llm_caret/workbench/tui_entry.spl`
- `src/app/llm_caret/workbench/tui_view.spl`
- `src/app/llm_caret/gui.spl`
- `src/app/llm_caret/main.spl`
- `src/app/llm_caret/multi_caret_manager.spl`

Current contract: pane_team launches real Smux piped children and feeds their identity to ManagedAgent; pane_source captures via direct smux_capture. Shared UI/session models are projections, not authority.

Owner prerequisite: Workbench owner: preserve exactly one authoritative child per agent; consume typed snapshots/events/capture rather than copy ServiceState; bind existing semantic UI to CoreMux, not a replacement renderer.

Required command mapping: `CreateSession`, `CreateWindow`, `LaunchPane`, `SplitPane`, `FocusWindow`, `FocusPane`, `ResizeWindow`, `ToggleZoom`, `SendLiteral`, `SendKeys`, `Paste`, `Notify`, `DetachClient`, `TerminatePane`. Common queries/lease/recovery apply.

Optional extension handling: GUI/TUI may acquire stronger layout/overlay leases after core admission; missing extras leave the ordinary child UI usable and visibly disabled. Mandatory-operation refusal blocks this consumer workflow; it is never a successful no-op.

Acceptance anchors:

- `test/03_system/app/llm_caret/caret_workbench_prod_spec.spl` (existing; inspect its actual evidence boundary before reuse).
- `test/03_system/app/llm_caret/caret_workbench_e2e_spec.spl` (existing; inspect its actual evidence boundary before reuse).
- `test/03_system/app/llm_caret/workspace_embed_parity_system_spec.spl` (existing; inspect its actual evidence boundary before reuse).

- **A03-S1 / NOT_RUN:** Start actual team and prove manager PID/owner pane refer to the same independently ready child; child transforms a fresh nonce visible in GUI and TUI.
- **A03-S2 / NOT_RUN:** Switch real session/window focus, send input/messages, resize/zoom and observe the selected child only; slow capture consumer preserves declared continuation/backpressure.
- **A03-S3 / NOT_RUN:** Close/reopen GUI/TUI view while session persists; crash one client and recover capacity; terminate owned children and reconcile manager state without duplicate spawn.

### A04 - Hosted Smux product

Existing paths:

- `src/app/hosted_apps/smux_client.spl`
- `src/app/hosted_apps/apps/smux/smux_remote.spl`
- `src/os/apps/smux/server.spl`
- `src/os/apps/smux/smux_remote.spl`
- `src/os/apps/smux/interactive_client.spl`

Current contract: Existing serve/request/attach and legacy interactive line protocol; new framed SDN SDK must use an explicitly registered separate route. Server foundations do not prove complete CoreMux admission.

Owner prerequisite: Smux server/host composition owners: connect existing sole service authority to authenticated framed dispatcher and all mandatory operations; preserve old protocol and CLI output; coordinate current common validation/API/metadata-helper writer.

Required command mapping: `CreateSession`, `CreateWindow`, `LaunchPane`, `SplitPane`, `AttachClient`, `DetachClient`, `SetClientViewport`, `FocusWindow`, `FocusPane`, `ResizePane`, `ResizeWindow`, `SelectLayout`, `ToggleZoom`, `SendLiteral`, `SendKeys`, `Notify`, `StopOwnedNamespace`. Common queries/lease/recovery apply.

Optional extension handling: No optional extension is necessary for this baseline; any added extension must use separate acquisition and refusal assertions. Mandatory-operation refusal blocks this consumer workflow; it is never a successful no-op.

Acceptance anchors:

- `test/03_system/tools/coremux_sosix_endpoint_spec.spl` (existing; inspect its actual evidence boundary before reuse).
- `test/03_system/tools/smux_windows_owner_lifecycle_spec.spl` (existing; inspect its actual evidence boundary before reuse).
- `test/03_system/tools/smux_windows_shared_clients_spec.spl` (existing; inspect its actual evidence boundary before reuse).
- `test/03_system/tools/smux_major_features_phase3_spec.spl` (existing; inspect its actual evidence boundary before reuse).

- **A04-S1 / NOT_RUN:** Launch real hosted server/product plus two independent clients; exercise help/invalid CLI and authenticated framed route without treating old line replies as SDN.
- **A04-S2 / NOT_RUN:** Observe both split children independently ready, nested geometry and child-reported dimensions; legacy client and CoreMux client mutations share one revision/identity owner.
- **A04-S3 / NOT_RUN:** Detach/reconnect/crash clients, expire leases and reconcile an uncertain mutation by RequestStatus; pending cleanup stays failure until terminal owner guard confirms release.

### A05 - OS shell / packaged Smux

Existing paths:

- `src/os/apps/smux/smux_app.spl`
- `src/os/tools/shell/register_tools.spl`

Current contract: Smux application/service routes exposed through shell/loader registries; registry labels and model dashboards are not guest execution.

Owner prerequisite: Shell/OS composition owner: bind selected provider through actual package/loader entry, preserve stable Sosix host API; guest route needs qualified image and terminal owner, cannot inherit host-only evidence.

Required command mapping: `CreateSession`, `LaunchPane`, `SplitPane`, `FocusPane`, `ResizePane`, `SelectLayout`, `ToggleZoom`, `SendLiteral`, `SendKeys`, `AttachClient`, `DetachClient`, `TerminateSession`. Common queries/lease/recovery apply.

Optional extension handling: No optional extension is necessary for this baseline; any added extension must use separate acquisition and refusal assertions. Mandatory-operation refusal blocks this consumer workflow; it is never a successful no-op.

Acceptance anchors:

- `test/03_system/app/simpleos/feature/tmux_simpleos_spec.spl` (existing; inspect its actual evidence boundary before reuse).

- **A05-S1 / NOT_RUN:** Launch registered hosted-shell Smux command as a real process and confirm child nonce through actual terminal.
- **A05-S2 / NOT_RUN:** Where guest route is claimed, boot real image and invoke package through loader; child input/dimensions/layout must be observed inside guest.
- **A05-S3 / NOT_RUN:** Detach/reopen and terminate only owned session through shell command; missing guest fixture is BLOCKED, never replaced by mux_model assertions.

### A06 - Web dashboard

Existing paths:

- `src/app/web_dashboard/server.spl`
- `src/app/web_dashboard/tmux_api.spl`
- `src/app/web_dashboard/terminal_ws.spl`

Current contract: HTTP /api/tmux is now mounted to checked std.tmux.mod behind real auth lookup and same-origin gate, superseding old fixed-200 inventory gap. terminal_ws still directly imports std.tmux; its mounted authenticated live path is not established by this audit.

Owner prerequisite: Web owner: inject backend-selected CoreMux at authenticated route and WS boundaries; preserve public JSON HTTP/WS interoperability; retain login/session revocation/CSRF checks; typed errors must propagate instead of empty successful lists.

Required command mapping: `CreateSession`, `TerminateSession`, `CreateWindow`, `LaunchPane`, `ResizePane`, `ResizeWindow`, `SendLiteral`, `SendKeys`, `Paste`, `SubmitShellCommand`, `AttachClient`, `DetachClient`. Common queries/lease/recovery apply.

Optional extension handling: No optional extension is necessary for this baseline; any added extension must use separate acquisition and refusal assertions. Mandatory-operation refusal blocks this consumer workflow; it is never a successful no-op.

Acceptance anchors:

- `test/03_system/app/web_dashboard/feature/tmux_api_route_spec.spl` (existing; inspect its actual evidence boundary before reuse).
- `test/03_system/app/web_dashboard/feature/shared_mux_system_spec.spl` (reserved; no spec/fixture implied).

- **A06-S1 / NOT_RUN:** Start actual HTTP server with private provisioned credentials, login and create/list real session on selected backend; wrong/missing credentials and fabricated cookies fail.
- **A06-S2 / NOT_RUN:** Open authenticated actual WebSocket, send literal text/keys and resize; independently observe real child output/dimensions and browser rendering, not direct handler invocation.
- **A06-S3 / NOT_RUN:** Reconnect socket and revoke operator session; foreign targets and stale refs fail; background child policy preserved and final authorized cleanup has pending=false plus external quiescence.

### A07 - LLM dashboard terminal

Existing paths:

- `src/app/llm_dashboard/gui/tmux_panel.spl`
- `src/app/llm_dashboard/gui/terminal_panel.spl`
- `src/app/llm_dashboard/gui/html_views.spl`

Current contract: GUI tmux/terminal panels use direct std.tmux facade and TCP/WS handlers; HTML and handler definitions do not establish active mounted application route.

Owner prerequisite: LLM dashboard owner: identify and wire actual composition entry/route, reuse authenticated boundary and CoreMux provider rather than copying web registry/session authority; resolve legacy indices once to owner refs.

Required command mapping: `CreateSession`, `TerminateSession`, `CreateWindow`, `LaunchPane`, `ResizePane`, `SelectLayout`, `ToggleZoom`, `SendLiteral`, `SendKeys`, `Paste`, `SubmitShellCommand`, `Notify`, `AttachClient`, `DetachClient`. Common queries/lease/recovery apply.

Optional extension handling: GUI/TUI may acquire stronger layout/overlay leases after core admission; missing extras leave the ordinary child UI usable and visibly disabled. Mandatory-operation refusal blocks this consumer workflow; it is never a successful no-op.

Acceptance anchors:

- `test/03_system/app/llm_dashboard/feature/shared_mux_system_spec.spl` (reserved; no spec/fixture implied).

- **A07-S1 / NOT_RUN:** Launch actual dashboard and activate terminal through its real UI/HTTP route; independently ready child and selected backend must be observable.
- **A07-S2 / NOT_RUN:** Use two sessions/windows; focus, messages, literal input, layout/zoom/resize reach only intended pane and native terminal rendering matches owner state.
- **A07-S3 / NOT_RUN:** Disconnect/reopen view, revoke auth and refuse cross-namespace request; pending cleanup remains visible and owned process tree settles.

### A08 - Configured library / dynamic adapter consumers

Existing paths:

- `src/lib/gc_sync_mut/tmux/mod.spl`
- `src/lib/gc_async_mut/tmux/mod.spl`
- `src/lib/nogc_async_mut/tmux/mod.spl`
- `src/lib/nogc_sync_mut/tmux/mod.spl`
- `src/lib/nogc_sync_mut/tmux/__init__.spl`
- `src/lib/nogc_sync_mut/sosix/mux.spl`

Current contract: Existing tmux family forwarders end at real process facade; they are not separate providers. New SDK generic std.sosix.mux resolves to its explicit configured implementation; current client supports Smux ExistingOnly only.

Owner prerequisite: Configured-library and provider owners: maintain semantic --library-mode with generic app imports; no family-root source selection, copied facade or fallback. Implement supported selected-owner gaps and real Tmux CoreMux provider separately; runtime-discovered plugins join this map.

Required command mapping: `CreateSession`, `LaunchPane`, `AttachClient`, `DetachClient`, `SendLiteral`, `SendKeys`, `TerminateSession`. Common queries/lease/recovery apply.

Optional extension handling: No optional extension is necessary for this baseline; any added extension must use separate acquisition and refusal assertions. Mandatory-operation refusal blocks this consumer workflow; it is never a successful no-op.

Acceptance anchors:

- `test/03_system/tools/coremux_sosix_endpoint_spec.spl` (existing; inspect its actual evidence boundary before reuse).

- **A08-S1 / NOT_RUN:** Compile actual consumer using each claimed supported mode and broad roots; verify selected implementation identity plus real child value/output, not just import success.
- **A08-S2 / NOT_RUN:** Missing selected owner/symbol fails attributable without other-family fallback; interleave two configured modes and fresh/warm caches using actual consumer semantics.
- **A08-S3 / NOT_RUN:** Select Tmux with actual backend provider on compatible host; absence is BLOCKED/Unsupported admission, not Smux substitution; namespace cleanup remains owned.

### A09 - IDE/editor/extension integration

Existing paths:

- `src/app/ide/main.spl`
- `src/app/editor/gui_shell.spl`
- `src/app/editor/tui_shell.spl`
- `src/lib/editor/view/terminal_panel.spl`
- `src/lib/editor/core/plugin_host.spl`
- `src/lib/editor/extensions/host.spl`

Current contract: IDE delegates to editor GUI/TUI; terminal_panel renders supplied lines, legacy plugin registry and active extension manifest host are not demonstrated live CoreMux routes.

Owner prerequisite: IDE/extension owner UNASSIGNED: implement actual extension/command-to-CoreMux composition and idle lease scheduling, reuse existing shared semantic Caret UI; pane refs remain owner-issued, views do not own background lifetime.

Required command mapping: `CreateSession`, `CreateWindow`, `LaunchPane`, `SplitPane`, `FocusWindow`, `FocusPane`, `ResizePane`, `ResizeWindow`, `ToggleZoom`, `SendLiteral`, `SendKeys`, `Paste`, `Notify`, `AttachClient`, `DetachClient`, `TerminatePane`. Common queries/lease/recovery apply.

Optional extension handling: GUI/TUI may acquire stronger layout/overlay leases after core admission; missing extras leave the ordinary child UI usable and visibly disabled. Mandatory-operation refusal blocks this consumer workflow; it is never a successful no-op.

Acceptance anchors:

- `test/03_system/app/ide/feature/ide_core_mux_system_spec.spl` (reserved; no spec/fixture implied).

- **A09-S1 / NOT_RUN:** Launch actual IDE GUI/TUI, invoke registered Caret terminal command and open independently ready real child; manifest activation alone fails acceptance.
- **A09-S2 / NOT_RUN:** Create two windows with directional nested splits; focus/message/input and zoom/resize reflect real child state and existing semantic widgets.
- **A09-S3 / NOT_RUN:** Close/reopen terminal view, crash extension/client, reclaim capacity and refuse stale refs; explicit terminate cleans owned children without destroying unrelated IDE/workspace sessions.

### A10 - Swarm / modeled terminal consumers

Existing paths:

- `src/app/llm_caret/claude_full/utils/swarm/backends/TmuxBackend.spl`
- `src/app/llm_caret/claude_full/utils/swarm/backends/PaneBackendExecutor.spl`
- `src/app/llm_caret/claude_full/utils/terminalPanel.spl`
- `src/app/llm_caret/agent_tmux.spl`
- `src/app/llm_caret/agent_manager_view.spl`

Current contract: Synthetic IDs/command accumulation and supplied usage/terminal models; no actual spawn demonstrated by these model paths.

Owner prerequisite: Caret swarm owner: replace synthetic execution adapter with injected production CoreMux workflow, keep pure display models as projections; assign runtime-selected backends explicitly and preserve sender/agent identity.

Required command mapping: `CreateSession`, `CreateWindow`, `LaunchPane`, `SplitPane`, `FocusPane`, `SendLiteral`, `SendKeys`, `SubmitShellCommand`, `Notify`, `DetachClient`, `TerminatePane`. Common queries/lease/recovery apply.

Optional extension handling: GUI/TUI may acquire stronger layout/overlay leases after core admission; missing extras leave the ordinary child UI usable and visibly disabled. Mandatory-operation refusal blocks this consumer workflow; it is never a successful no-op.

Acceptance anchors:

- `test/03_system/app/llm_caret/feature/caret_mux_swarm_system_spec.spl` (reserved; no spec/fixture implied).

- **A10-S1 / NOT_RUN:** Launch real swarm consumer with two actual ready agents; commands must execute in those children, never pass from appended command strings or synthetic IDs.
- **A10-S2 / NOT_RUN:** Route messages/output and pane selection through actual team/UI; validate independent nonces, Unicode capture and recipient isolation across namespaces.
- **A10-S3 / NOT_RUN:** Kill one agent/client, reconcile owner exit events and restart with fresh incarnation; detach persists intended background work then owned cleanup completes.

## Backend cohorts, N2 and execution gates

A01-A03 and A06-A10 require real workflows on both Smux and Tmux after their providers exist. A04/A05 are actual Smux product/host routes; Tmux supplies the independent shared semantic/legacy compatibility reference cohort, not a replacement Smux executable or falsely named guest backend. Platform-unavailable Tmux/guest cohorts remain BLOCKED with a qualified compatible host requirement; no backend is silently substituted. Every runtime-discovered consumer inherits this rule.

Accepted N2 stays unchanged: each backend needs two namespaces, two sessions per namespace, four panes and two clients per namespace (eight panes/four clients total), configurable stronger topology, limits and one-over-limit refusal. Run actual 24-hour background/reconnect soak per backend, including floods, slow readers, crash recovery, lease expiry, concurrent layout conflicts, Unicode and alternate screen. A short test is diagnostic only. Record warm p95 metadata <=100ms and independently settled layout <=250ms, cold setup separately, baseline/peak/settled RSS, process/handle counts, queue/capture bounds and cleanup. No values are claimed measured here.

Latest user authorization permits existing verified Phase 2 for interim feature tests, without rebuilding Phase 2. Retain P2 generation/runtime/source receipts and exact capability checks; that evidence does not become Phase 3 qualification. P3 claims still require genuine P3 producer/runtime/Hello lineage and matching full CLI/canonical runner. Source authoring or successful compiler probes are not product execution. The exhausted six-attempt cache-generator series remains closed; this migration map grants no retry, new build, or reset of feature history.

Before implementation/execution: freeze complete provider interface and actual support; assign consumer owners; admit source/product/compiler/runtime/host and isolated namespace credentials; ensure real fixture cleanup and independent process-tree guard; schedule finite root-owned rows. Missing application route, provider, terminal/guest fixture or runner must be BLOCKED/NOT_RUN, never skip-as-pass. On actual missing fixture a runnable scenario fails its setup with retained evidence.

SDN results must record per-backend/per-consumer planned, discovered, executed, passed, failed, blocked and not-run counts; source/product/producer/runtime/host hashes; exact argv; timestamps; child incarnation/PID plus independent readiness; scoped before/after metadata, child I/O, geometry, messages/render ACKs, continuation/revision receipts; and cleanup pending state/terminal quiescence. PID absence alone is not full cleanup proof (provider semantics and PID reuse remain relevant). Preserve failing artifacts before owner repair, rerun only affected criteria within the cross-session six-cycle cap, reuse unchanged green checks. No consumer or backend is complete until real application assertions pass. Landing requires those actual tests plus independent exact-head review; this plan is not a landing approval.

Plan accounting: ten consumer groups and thirty proposed workflow cases, zero new executable specs, zero executed cases, zero observed PASS/FAIL from this task. Existing historical failures and source reviews remain intact. The machine-readable map preserves all 84 inherited source-hit paths separately from actual consumer paths; catalog membership is not an execution/support claim.
