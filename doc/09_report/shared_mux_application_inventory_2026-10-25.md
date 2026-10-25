# Shared pane/mux application inventory

Date: 2026-10-25. Worktree: `simple-smux-phase3-suite-20261025`, baseline
`release/1.0.0` at `1e431722b40236eda5e80bd5f5bf06395b0d0d08`, with concurrent
owned source changes present. This is a read-only caller audit, not executed
feature evidence. User scope includes Caret, IDE integration and every application
using the shared API; these are mandatory REQ-CMUX-012 obligations.

## Method and limits

One bounded owned-`src` search inspected `.spl` imports/calls for smux, tmux,
shared pane operations, CoreMux and dynamic selectors. Vendored runtime/compiler
trees were excluded. It found **1,367 matched lines in 84 files**. Narrow
follow-up reads checked only those owners and IDE/editor/plugin integration
paths; no repeated full-tree source scan was performed. Raw lines and path list
are retained at `build/caret-mux-inventory/{callers.raw.txt,paths.txt}`; the
IDE/plugin follow-up is `ide-plugin.raw.txt`. Counts describe source hits, not
applications, executed cases or feature support.

The classified catalog below accounts for the discovered families. Runtime
plugin loading, externally supplied commands and computed imports still require
execution-time provider/dispatch receipts. Absence from a lexical search is not
proof that no dynamic caller exists. New discovered runtime callers must be
assigned to the same mandatory matrix, not silently excluded from acceptance.

## Actual callers and required system evidence

Every row starts **NOT_RUN** for current CoreMux qualification. Existing test
paths are reuse candidates; their models/fixtures must not be promoted to live
evidence without executing the actual application. Reserved paths do not imply
an implemented spec or fixture.

| ID / caller surface | Inspected production path and classification | Required real scenario / test owner |
| --- | --- | --- |
| A01 Caret cs dashboard | `llm_caret/pane_backend.spl` invokes the real in-process smux owner or actual tmux process; `cs_dashboard.spl` and `cs_main.spl` consume it. `CS_PANE_BACKEND=tmux` selects tmux only if a probe succeeds, otherwise silently chooses smux; Windows probe unconditionally refuses tmux. This conflicts with new explicit selection semantics. | Actual dashboard launch, agent child argv/cwd/env, literal/paste/key separation, layout/zoom/title/hide/rebalance, messages and detach/cleanup on each selected backend. Reuse `test/03_system/app/llm_caret/caret_suite_tmux_window_system_spec.spl`; shared semantic assertions belong to reserved `feature/caret_mux_tui_spec.spl`, not a wrapper around the old spec. |
| A02 Caret workspace CLI | `agent_workspace.spl` launches actual `tmux -V` and private `-L caret_ws_ID` calls; `workspace_cli.spl` consumes them. Separate lifecycle from dashboard. | Launch workspace CLI as a process in two namespaces, ensure/create/discover/rename windows, broadcast excluding the real sender, reconnect and namespace-specific teardown. Reuse `workspace_cli_system_spec.spl`, `workspace_recovery_system_spec.spl`, `agent_team_workspace_system_spec.spl` under `test/03_system/app/llm_caret/`. Exact audited flags/formats remain mandatory. |
| A03 Caret workbench GUI/TUI | `workbench/pane_team.spl` creates real piped children via smux; `pane_source.spl` captures and publishes actual output. `session_source.spl`, `session_contract.spl`, `tui_view.spl`, `tui_entry.spl`, `gui.spl`, `main.spl`, `multi_caret_manager.spl` consume/publish the shared state. Display state is not itself child authority. | Launch actual team/workbench, correlate manager/owner child identity, deliver messages, observe real GUI/TUI output and input, switch window/session, close a view without killing retained sessions, then terminate owned children. Reuse `caret_workbench_prod_spec.spl`, `caret_workbench_e2e_spec.spl`, `workspace_embed_parity_system_spec.spl`; retain their narrower source/model assertions separately. |
| A04 Hosted SMUX product | `hosted_apps/smux_client.spl` routes serve/request/attach to actual owners; `hosted_apps/apps/smux/smux_remote.spl` routes stdin-owner entry. `os/apps/smux/server`, `smux_remote`, `interactive_client` provide process/transport paths. | Actual Phase 3-built product, help/invalid argument sanity, two real interactive clients, independent server, nested split/layout/child size, background messages and terminal cleanup. Reuse existing Windows owner/interactive/shared-client native fixtures and SMUX SSpecs. New three-case `smux_major_features_phase3_spec.spl` proves composition geometry only. |
| A05 OS shell / packaged SMUX | `os/apps/smux/smux_app.spl` invokes actual service/PTY operations; `os/tools/shell/register_tools.spl`, loader registries and package manifests expose product routes. Registry/manifest labels do not prove executable loading. `smux_dashboard`/`mux_model` also have model-only paths. | Run the admitted hosted shell route and, where the registered guest route is claimed, the real image/application loader plus child terminal. Reuse `test/03_system/app/simpleos/feature/tmux_simpleos_spec.spl` only at its actual evidence boundary. Missing bootable/qualified owner is BLOCKED; a host model cannot satisfy guest launch. |
| A06 Web dashboard | `web_dashboard/tmux_api.spl` and `terminal_ws.spl` call real tmux facade operations. **Routing gap:** inspected `server.spl:231` returns fixed HTTP 200 `[]` for `/api/tmux`; targeted references found handler definitions but no connected route. HTML request strings are labels/requests, not execution. | Reserved `test/03_system/app/web_dashboard/feature/shared_mux_system_spec.spl`: start real server, create/list via actual HTTP, attach real WS, send input and independently observe child output/resize; reconnect and cleanup. Must wire production routes first. Calling handler functions directly cannot qualify the server path. |
| A07 LLM dashboard terminal | `llm_dashboard/gui/tmux_panel.spl` and `terminal_panel.spl` invoke facade functions; `html_views.spl` renders a terminal surface. Targeted inspection found handler definitions, not proof of mounted request routing. | Reserved `test/03_system/app/llm_dashboard/feature/shared_mux_system_spec.spl`: actual dashboard HTTP/WS round-trip to a real child on both backends, focus/session isolation, messages, layout and cleanup. Mounted owner and native browser/terminal evidence are prerequisites. |
| A08 Standard-library configured callers | `std.tmux` has GC/concurrency forwarding families: `gc_sync_mut -> gc_async_mut -> nogc_async_mut -> nogc_sync_mut`. Final `nogc_sync_mut/tmux/mod.spl` invokes shell/process commands via `std.io_runtime`; `__init__.spl` reexports. Different facades are not independent backend implementations. | Reuse shared contract fixture compiled with each applicable configured family selected through the real application composition. Record selected family/provider. Probe actual process and output, negative failures and cleanup. Do not globally force the nogc family or infer all variants work from one symbol export. |
| A09 IDE/editor/extension integration | `app/ide/main.spl` delegates to editor GUI/TUI; GUI `caret` profile activates the Simple language only. `lib/editor/view/terminal_panel.spl` stores/renders supplied lines, not a terminal owner. `lib/editor/core/plugin_host.spl` is a legacy registry; active `extensions/host.spl` loads manifests, with no direct mux call found in focused inspection. **No demonstrated live CoreMux IDE path.** | Reserved `test/03_system/app/ide/feature/ide_core_mux_system_spec.spl`: launch the actual IDE, activate actual extension/command, open a real Caret/terminal child, operate two windows/splits, route messages/input, resize/zoom and close/reopen. Verify real native output and owned-resource cleanup. Missing integration is a deliverable/blocker, not an excluded optional case. Reuse office/plugin lifecycle fixtures where applicable; do not count registry activation as terminal execution. |
| A10 Modeled swarm/terminal scaffolding | `claude_full/utils/swarm/backends/{TmuxBackend,PaneBackendExecutor}.spl` append commands/synthetic IDs and model bookkeeping; `terminalPanel.spl` models state. `agent_tmux.spl`/`agent_manager_view.spl` render supplied process usage. No real spawn is established by these paths. | Required real swarm/agent consumer workflow must be wired to production CoreMux before qualification. Reserve `test/03_system/app/llm_caret/feature/caret_mux_swarm_system_spec.spl` only once wired. Existing `llm_caret_embedded_tmux_tui_spec.spl` explicitly tests supplied model values and remains model evidence. |

All paths in the production column are relative to `src/`. A01–A10 each require
backend applicability recorded explicitly. Real tmux absence on the Windows host
is BLOCKED for that backend cohort, not permission to substitute smux. A qualified
compatible tmux host may supply its own separately pinned product/runtime/host
receipts. CoreMux semantic and Caret compatibility expectations stay the same.

## Labels, support owners and exclusions

- `claude_full/commands/{init_verifiers,terminalSetup/terminalSetup}.spl`,
  `components/{LogoV2/LogoV2,messageActions}.spl`, `utils/configConstants.spl`
  and `utils/worktree.spl` carry environment detection, commands, metadata or
  display references. They are not additional mux server implementations; any
  dynamically launched terminal command still needs A01/A02/A10 execution proof.
- `lib/common/{tmux_session_model,primary_cli_model,simple_os_primary}.spl`
  and SMUX model/contract/layout modules define values/rendering/geometry; their
  pure assertions support A04/A05 but do not replace live owners.
- `lib/common/contracts/mux/{core_v1,validation_v1}.spl` are the current bounded
  discovery contract/validation slice. Their presence does not prove providers,
  complete CoreMux operations or any migrated application.
- SMUX service/API, frame, VT, notification, lease, target and checkpoint modules
  are production support owners shared by A01/A03/A04/A05, not separate apps.
- OS loader registries, seeded/builtin manifests, QEMU scenario disk/exec helpers
  and package lists are A05 launch prerequisites. The shell less-tool detection
  of a terminal environment is not a mux caller.
- `compiler/20.hir/hir_lowering/types.spl`, `lib/text.spl`,
  `nogc_sync_mut/io/resource_scope.spl` and `common/term/emulator.spl` include
  naming/comment/terminal compatibility matches; no separate application is
  inferred from those hits. Vendored/third-party runtime was not included.

## Result accounting and next work

No compiler, backend, IDE or dashboard process ran in this audit. New shared
system cases discovered/executed/passed/failed: **0/0/0/0**; zero failures is not
a PASS because all required application rows are NOT_RUN. Missing routes and
provider/Phase 3 prerequisites are blockers, not fabricated executed failures.
Existing authored specs and historical failures retain their actual status and
producer identity. The current source scan cannot supply binary-owned counts.

Each future row must retain SDN status and source/product/compiler/runtime/host
identities, actual binary-owned case counts (passed, failed, blocked, not run),
command/process/terminal evidence, logs, output/capture hashes, layout/message
receipts and cleanup/quiescence. Preserve actual failed output before repair;
rerun only affected criteria after a material fix, within the shared six-cycle
cap. Never replace an application failure with a passing adapter/model test.

The system and agent plans own A01–A10 assignments and prerequisites. Every
runtime-discovered shared API consumer must be added there before completion.
The application scope is not closed until Caret, IDE and all actual consumers
have real system evidence, in addition to both-backend N2 qualification.

## Exact bounded source-hit catalog

These are the 84 source hits classified above; membership does not imply a live caller.

### src/app/hosted_apps

- `src/app/hosted_apps/apps/smux/smux_remote.spl`
- `src/app/hosted_apps/smux_client.spl`

### src/app/llm_caret

- `src/app/llm_caret/agent_manager_view.spl`
- `src/app/llm_caret/agent_tmux.spl`
- `src/app/llm_caret/agent_workspace.spl`
- `src/app/llm_caret/claude_full/commands/init_verifiers.spl`
- `src/app/llm_caret/claude_full/commands/terminalSetup/terminalSetup.spl`
- `src/app/llm_caret/claude_full/components/LogoV2/LogoV2.spl`
- `src/app/llm_caret/claude_full/components/messageActions.spl`
- `src/app/llm_caret/claude_full/utils/configConstants.spl`
- `src/app/llm_caret/claude_full/utils/swarm/backends/PaneBackendExecutor.spl`
- `src/app/llm_caret/claude_full/utils/swarm/backends/TmuxBackend.spl`
- `src/app/llm_caret/claude_full/utils/terminalPanel.spl`
- `src/app/llm_caret/claude_full/utils/worktree.spl`
- `src/app/llm_caret/cs_dashboard.spl`
- `src/app/llm_caret/cs_main.spl`
- `src/app/llm_caret/gui.spl`
- `src/app/llm_caret/main.spl`
- `src/app/llm_caret/multi_caret_manager.spl`
- `src/app/llm_caret/pane_backend.spl`
- `src/app/llm_caret/workbench/pane_source.spl`
- `src/app/llm_caret/workbench/pane_team.spl`
- `src/app/llm_caret/workbench/session_contract.spl`
- `src/app/llm_caret/workbench/session_source.spl`
- `src/app/llm_caret/workbench/tui_entry.spl`
- `src/app/llm_caret/workbench/tui_view.spl`
- `src/app/llm_caret/workspace_cli.spl`

### src/app/llm_dashboard

- `src/app/llm_dashboard/gui/html_views.spl`
- `src/app/llm_dashboard/gui/terminal_panel.spl`
- `src/app/llm_dashboard/gui/tmux_panel.spl`

### src/app/web_dashboard

- `src/app/web_dashboard/dashboard_html.spl`
- `src/app/web_dashboard/server.spl`
- `src/app/web_dashboard/terminal_ws.spl`
- `src/app/web_dashboard/tmux_api.spl`

### src/compiler/20.hir

- `src/compiler/20.hir/hir_lowering/types.spl`

### src/lib/common

- `src/lib/common/contracts/mux/core_v1.spl`
- `src/lib/common/contracts/mux/validation_v1.spl`
- `src/lib/common/primary_cli_model.spl`
- `src/lib/common/simple_os_primary.spl`
- `src/lib/common/term/emulator.spl`
- `src/lib/common/tmux_session_model.spl`

### src/lib/gc_async_mut

- `src/lib/gc_async_mut/tmux/mod.spl`

### src/lib/gc_sync_mut

- `src/lib/gc_sync_mut/tmux/mod.spl`

### src/lib/nogc_async_mut

- `src/lib/nogc_async_mut/tmux/mod.spl`

### src/lib/nogc_sync_mut

- `src/lib/nogc_sync_mut/io/resource_scope.spl`
- `src/lib/nogc_sync_mut/tmux/__init__.spl`
- `src/lib/nogc_sync_mut/tmux/mod.spl`

### src/lib/text.spl

- `src/lib/text.spl`

### src/os/_QemuRunner

- `src/os/_QemuRunner/scenario_disks.spl`
- `src/os/_QemuRunner/scenario_exec.spl`

### src/os/apps

- `src/os/apps/smux/api.spl`
- `src/os/apps/smux/backend_native.spl`
- `src/os/apps/smux/client_leases.spl`
- `src/os/apps/smux/client_notifications.spl`
- `src/os/apps/smux/client_view.spl`
- `src/os/apps/smux/contract.spl`
- `src/os/apps/smux/frame_snapshot.spl`
- `src/os/apps/smux/interactive_client.spl`
- `src/os/apps/smux/interactive_protocol.spl`
- `src/os/apps/smux/layout.spl`
- `src/os/apps/smux/mod.spl`
- `src/os/apps/smux/mux_model.spl`
- `src/os/apps/smux/mux_rects.spl`
- `src/os/apps/smux/notification_client.spl`
- `src/os/apps/smux/notification_protocol.spl`
- `src/os/apps/smux/server.spl`
- `src/os/apps/smux/service.spl`
- `src/os/apps/smux/session_lifecycle.spl`
- `src/os/apps/smux/session_targets.spl`
- `src/os/apps/smux/smux_api.spl`
- `src/os/apps/smux/smux_app.spl`
- `src/os/apps/smux/smux_contract.spl`
- `src/os/apps/smux/smux_dashboard.spl`
- `src/os/apps/smux/smux_remote.spl`
- `src/os/apps/smux/split_checkpoint.spl`
- `src/os/apps/smux/vt_screen.spl`
- `src/os/apps/smux/window_layout_service.spl`

### src/os/kernel

- `src/os/kernel/loader/app_registry.spl`
- `src/os/kernel/loader/builtin_binary_registry.spl`
- `src/os/kernel/loader/disk_launch_manifest.spl`
- `src/os/kernel/loader/seeded_app_registry.spl`

### src/os/packages

- `src/os/packages/os_packages.spl`

### src/os/tools

- `src/os/tools/shell/less/less_tool.spl`
- `src/os/tools/shell/register_tools.spl`
