# Caret Workbench UI — Evidence and Competitive Research

**Date:** 2026-11-14
**Target:** `ormastes/simple`, `release/1.0.0`
**Inspected HEAD (original plan):** `52caab0725c0d975d8ce69c351780efe8db2210e`
**Re-verified against:** `origin/release/1.0.0` @ `e3b68584142` (2026-11-14). See the last column of § 1.1 and the table in § 1.3.
**Status:** Research input to a proposed plan. This is a proposed plan, not a release-readiness certificate. Nothing in the Caret workbench UI program is release-qualified.

Related docs (same program):
- Design: [caret_workbench_ui.md](../../../05_design/app/llm_caret/caret_workbench_ui.md)
- Requirements: [caret_workbench_ui.md](../../../02_requirements/app/llm_caret/caret_workbench_ui.md)
- Plan: [caret_workbench_ui_plan.md](../../../03_plan/app/llm_caret/caret_workbench_ui_plan.md)
- TLDR: [caret_workbench_ui_research_2026-11-14_tldr.md](caret_workbench_ui_research_2026-11-14_tldr.md)

Re-verification method: the cited file was opened or grepped for the cited symbol on the commit above. Verdicts are `confirmed`, `changed: <what>`, or `could not verify: <why>`. "Could not verify" means the claim was not checked in this pass, not that it is false. No binary was run and no screen was captured.

## 1. Evidence and boundaries

### 1.1 Inspected `release/1.0.0` source

| Area | Source and direct finding | Interpretation | Re-verified 2026-11-14 @ e3b68584142 |
|---|---|---|---|
| Caret dashboard | `src/app/llm_caret/cs_dashboard.spl`: roster, selected, `/switch`, `/max`, `/key`, status and bottom input | A working dashboard implementation exists in source; reuse it, but it is not proof of the entire desired interactive GUI | could not verify: file exists; `/switch`, `/max`, `/key` handlers not grepped |
| Caret live loop | `src/app/llm_caret/cs_main.spl`: 50ms input tick, 200ms pane poll, 2s roster refresh, changed-row repaint, plain fallback | Event-driven refactor must preserve the useful row diff; current input loop discards arrow/function-key escape sequences and live input is gated to POSIX | confirmed: `_CS_TICK_MS=50`, `_CS_POLL_MS=200`, `_CS_REFRESH_MS=2000` (cs_main.spl:111-115); escape sequences not treated as text input (:264); live loop gated to `platform == "posix"` with tty (:358-362) |
| Workbench TUI | `workbench/tui_layout.spl` and `tui_view.spl`: roster/details/composer, big active pane, preview strip, compact view | The source grid already matches the basic composition; current `_put_str` slices text by bytes and needs Unicode cell-width qualification | confirmed for `_put_str`: `tui_view.spl:51-56` loops `byte_len()` and `substring(i, i+1)` per cell (no cell-width handling); `tui_layout.spl` not opened |
| Workbench GUI | `workbench/gui_layout.spl` and `gui_page.spl`: connection labels, per-session draft state, HTML/CSS roster/composer/active/previews | A source-rendered HTML projection exists; real input/resize/attach behavior must be qualified; preview card bodies in this renderer are empty | could not verify: `gui_page.spl` exists and carries per-session draft handling; empty preview-card bodies not confirmed |
| Session projection | `workbench/session_source.spl`: manager→session adapter; `MANAGED_PROVIDER = "process"`, `AgentTurn.Unknown`, `needs_attention: false`, initial generation | Critical missing semantic status and provider identity in this path; false certainty must not be added in UI | confirmed: `MANAGED_PROVIDER = "process"` (session_source.spl:79), `turn: AgentTurn.Unknown` (:96), `needs_attention: false` (:99); initial generation not checked |
| Pane projection | `workbench/pane_source.spl` explicitly says its captured smux child is **not** necessarily the manager's child | Critical identity seam; cannot yet treat selected agent conversation and captured pane as authoritative identity without a new binding | confirmed: `pane_source.spl:14` says the pane's child is NOT one of the manager's agents |
| IDE launch | `src/app/ide/main.spl`: `--profile caret` forwarded to GUI profile, but `--tui` calls `editor_tui_run(session)` without profile | Caret profile parity for IDE TUI is an implementation seam | confirmed: `ide/main.spl:46,49` pass `launch.profile` to the GUI shells; `:52` still calls `editor_tui_run(_ide_session_for(launch))` with no profile |
| IDE GUI profile | `src/app/editor/gui_shell.spl`: Caret profile activates the Simple language instead of all builtin apps; it does not alone create the Caret docked view tree | Extend the existing host/profile activation path, not eager-load every office app | confirmed: `gui_shell.spl:71-76` caret profile activates only the Simple language; docked view tree not checked |
| Extension schema | `src/lib/editor/extensions/manifest.spl`, `contract.spl`, `host.spl`, `registry.spl`: commands/languages/debug adapters/themes/keybindings/custom editors, activation, permissions, host placement | VS Code-like view-container/panel/status/timeline contributions are **not present in inspected manifest** and need additive schema+host work | could not verify: all four files exist; a grep for `view_container|status_item|timeline|simple.ide.extension|panels` gave 6 hits in 4 files (manifest.spl 1, manifest_sdn.spl 2, builtin/md_language.spl 1, builtin/planner_ext.spl 2) that were not opened, so absence of v2 contributions is unconfirmed |
| Agent dashboard plugin | `src/lib/editor/extensions/builtin/agent_dashboard_ext.spl` contributes a tool-list command/language, not an agent roster view | Do not mistake a command manifest for the full UI | confirmed: header comment declares a document kind plus `agent-dashboard.*` command surface; no roster view |
| Native mux | `src/os/apps/smux/*`: service, frame capture, leases, input, notifications, owner/process contracts | Keep one smux authority; adapt it to typed workbench streams | changed: directory now also holds `runtime_binding_*_v3`, `runtime_control_*_v1`, `terminal_adoption_service_v2` and `terminal_settlement_service_v3` files (relevant to pane binding, not opened); named files present |
| Existing mux keys | `src/os/apps/smux/client_input.spl` uses `Ctrl+B` prefix and keys such as `c`, `n`, `o`, `z`, `d`, `%`, `"` | Must not reuse `Ctrl+B` as Caret global leader while native terminal focused | confirmed: `client_input.spl:43-56` treats byte 2 (Ctrl+B) as the prefix; unknown bindings pass through |
| Existing IDE keys | `src/lib/editor/00.common/keybindings.spl` reserves normal-mode `Ctrl+W`, `F5`, `F12`, `Ctrl+Space`, `Ctrl+.` etc. | Context-aware keybinding resolver is required; never globally steal editor/terminal keys | could not verify: file exists; reserved-key list not grepped |
| Trace queries | `src/app/traceability/query_options_v1.spl`: `list`, `show`, `refs`, `refs file`, worktree/index/git snapshots, `table`/`sdn` | Reuse actual query semantics; P0 structural results are unverified, group queries noted as P1 | could not verify: `query_options_v1.spl` exists (plus `query_main.spl`, `query_file_refs_v1.spl`); semantics and P0/P1 wording not opened |
| Native Slop | `src/app/slop/{projection,view,session,source,evidence,native_frame,native_host,main}.spl` | Real source slice exists; tests and native display/integration remain unqualified per its design checkpoint | confirmed present: all eight `src/app/slop` files exist; test and native-display qualification could not verify |

### 1.2 Current release blockers affect acceptance

- `doc/08_tracking/bug/native_llm_caret_smux_owner_spawned_as_interpreter_of_itself_2026-11-14.md` records an **open native Windows smux owner launch failure**: native Caret executes itself as though it were the `simple run` interpreter. The report states native workspace team scenario 3/4, interpreted 4/4. Fix the owner invocation/binding; don't bury this behind UI tests.
- `doc/08_tracking/bug/caret_smux_multi_launch_spec_marker_matched_pty_echo_2026-11-14.md` records a macOS spec race fixed by waiting for a child-computed marker, with its reported run moving 5/6→6/6. Tests that check terminal state must differentiate echoed commands from child-completed output.
- `src/app/slop` design checkpoint says runtime/native GUI selection/source/evidence capture and graph performance remain unqualified. Reuse code but do not present it as a finished graph widget.
- `src/app/llm_caret/workbench/gui_page.spl` contains an explicit `Option<SessionView>` compiler-resolution workaround. Preserve compatibility until the referenced compiler bug is actually fixed, then remove the workaround with a dedicated regression test.

This report is based on read-only inspection and official project research. **No live binary, actual Caret screen capture, build, UI interaction, provider login, or CI suite was executed**. The screenshots below are precise *design mockups*; reference product screenshots must be viewed at their official websites.


### 1.3 Re-verification of the § 1.2 blockers (2026-11-14 @ e3b68584142)

| Blocker | Re-verified result |
|---|---|
| Native smux owner launch bug (`native_llm_caret_smux_owner_spawned_as_interpreter_of_itself_2026-11-14.md`) | confirmed: file exists in `doc/08_tracking/bug/`, `Status: open`. changed: the file rates it `Severity: P2 (native-only)`, not an unqualified release blocker; the plan's "blocker" wording is the plan's own gating choice. The 3/4 vs 4/4 scenario counts were not re-checked. |
| macOS marker/PTY-echo spec race (`caret_smux_multi_launch_spec_marker_matched_pty_echo_2026-11-14.md`) | confirmed for the symptom and root cause (spec waited on a literal that the PTY echoed; failed 5/6 with `-1` columns). could not verify: the fix state and the 5/6 to 6/6 result (no status line was found by grep). |
| `src/app/slop` design checkpoint: native GUI capture and graph performance unqualified | could not verify: the checkpoint doc was not opened. |
| `gui_page.spl` `Option<SessionView>` workaround | confirmed: `gui_page.spl:22` comment says the lookup result is deliberately NOT `Option<SessionView>`. The cited compiler bug was not checked for a fix. |

### 1.4 Summary of changed or unverified rows

- changed: smux native owner row (new `runtime_binding_*_v3` / `runtime_control_*_v1` files exist); smux owner bug severity is P2.
- could not verify: dashboard `/switch /max /key`, GUI preview-card bodies, extension manifest v2 contribution absence, existing keybinding reservations, trace query P0/P1 wording, Slop qualification, bug-2 fix state, Slop checkpoint.
- confirmed: `_put_str` byte slicing, `MANAGED_PROVIDER`/`AgentTurn.Unknown`/`needs_attention: false`, pane_source identity caveat, IDE `--tui` ignoring the profile, Ctrl+B smux prefix, caret profile activating only the Simple language.

## 2. Competitive research and actionable choices

The names **Herd**, **herder** and **herdr** refer to different products. Their exact platform/current capabilities can change; the table reports the features documented at the reference URLs checked on this date.

| Tool | Valuable official pattern | Adopt | Avoid copying |
|---|---|---|---|
| [Herd](https://joinherd.ai/changelog) | Worktree per agent, sidebar diff stats/hotkeys, file tabs, source control, merge conflicts, run panel, attention badges, layout presets | Worktree and changes surfaced beside each agent; one-click review | Treating a copied visual hierarchy as actual process ownership |
| [herder](https://herder.sh/) | Fleet of hosts, accounts, provider CLIs, durable Board/approvals/child tasks, remote sessions and recovery | Host/task/child status and an action inbox | Coupling Core Caret to vendor-specific cloud/vault lifecycle |
| [herdr](https://github.com/rohanthewiz/herdr-go) | Native terminal panes, blocked/working/done/idle status, workspaces/tabs, pane hotkeys, attach/detach, screen-based detection | Terminal fidelity; optional screen heuristic adapter; fast pane navigation | Using terminal text as a trusted approval/security protocol |
| [Conductor](https://www.conductor.build/docs/guides/parallel-agents/run-multiple-claude-code-sessions) | Workspace = task worktree+branch+terminal+diff+checks+PR; separate chats may share workspace | Explicit task/workspace/session identity and review gate | Automatically making a new worktree for every conversation |
| [Superset](https://github.com/superset-sh/superset) | Large agent fleets, terminal splits, notifications, prompt editor, open-in-editor, diffs, ports/browser, remote CLI/MCP | Agent center + lightweight host handoff + multi-pane presets | Starting a parallel session host inside every editor client |
| [cmux](https://cmux.com/) | Notification rings, per-pane alerts, sidebar branch/ports, split/browser, OSC and hook alerts, socket automation | Attention rings and notification inbox; browser/dev-server panel | macOS-only renderer or OS-specific terminal assumptions |
| [VS Code Agents](https://code.visualstudio.com/docs/agents/run/agents-window) | Agent sessions list, pinned/unpinned active view, side-by-side editor, subagent inspection and worktree selection | Pinning rules; keep selected conversation while reading docs/trace; history | Assuming different harness sessions are always transferable |
| [VS Code extension API](https://code.visualstudio.com/api/extension-capabilities/extending-workbench) | Activity Bar, View Container, Tree View, Editor Group, Panel, Status Bar contributions | Add typed contribution points to Simple IDE host | Arbitrary untrusted webview with full workspace privilege |
| [Zed](https://zed.dev/docs/ai/agents) | Native agent, ACP external agent, and terminal thread are distinct session types | Explicit `Terminal` vs `Structured` view capability, same workspace | Replacing native CLIs with lossy chat transcript emulation |
| [OpenCode](https://opencode.ai/docs/build/plugins) | Server/TUI/GUI/RPC plugin facets share server-owned sessions and typed events | One service owner and multiple presentation plugins | Forking provider-specific UI state in clients |
| [Vibe Kanban](https://vibekanban.com/) | Task board, subissues, agent workspaces, diff review and QA | Optional task-board extension | Making Kanban the mandatory daily terminal UI; official site says product is sunsetting |

**Synthesis:** Caret should be **agent-aware terminal + IDE + traceability**, not just “tmux with badges” and not just “chat with an editor.” Its unique advantage is Simple's source/requirement/test/bug graph and mdsoc+ layered architecture integrated directly into agent actions.

## 16. References and source register

### External official product/architecture sources

1. [Herd website](https://joinherd.ai/) and [Herd changelog](https://joinherd.ai/changelog).
2. [herder](https://herder.sh/).
3. [herdr](https://github.com/rohanthewiz/herdr-go).
4. [Conductor: parallel Claude sessions](https://www.conductor.build/docs/guides/parallel-agents/run-multiple-claude-code-sessions) and [harness overview](https://www.conductor.build/docs/reference/harnesses).
5. [Superset README](https://github.com/superset-sh/superset).
6. [cmux](https://cmux.com/).
7. [VS Code: extending Workbench](https://code.visualstudio.com/api/extension-capabilities/extending-workbench), [Tree Views](https://code.visualstudio.com/api/extension-guides/tree-view), [Agents window](https://code.visualstudio.com/docs/agents/run/agents-window).
8. [Zed: agents](https://zed.dev/docs/ai/agents), [external agents](https://zed.dev/docs/ai/external-agents), [terminal threads](https://zed.dev/docs/ai/terminal-threads).
9. [OpenCode plugin architecture](https://opencode.ai/docs/build/plugins) and [TUI](https://opencode.ai/docs/tui/).
10. [Vibe Kanban](https://vibekanban.com/) (site notes sunsetting).

### Important Simple source/design references

- `src/app/llm_caret/{cs_dashboard,cs_main,pane_backend}.spl` and `src/app/llm_caret/workbench/{tui_layout,tui_view,gui_layout,gui_page,session_contract,session_source,pane_source}.spl`.
- `src/os/apps/smux/{client_input,service,api,core_mux_owner,client_attachment_service}.spl`.
- `src/app/ide/main.spl`, `src/app/editor/{gui_shell,tui_shell}.spl`, `src/lib/editor/extensions/*`, `src/lib/editor/00.common/keybindings.spl`.
- `src/app/traceability/*`, `src/app/slop/*`, `doc/05_design/infra/traceability_graph.md`, `doc/05_design/app/slop_viewer.md`, `doc/05_design/simple_traceability_sdn_slop_gui.md`.
- `doc/01_research/app/llm_caret/caret_suite_ide_workbench_smux_migration_2026-09-05.md` and earlier Caret production/orchestrator plans.
- `doc/07_guide/infra/traceability.md`, `doc/05_design/infra/traceability_link_operations_v2.md`, `config/traceability.sdn`.
- `doc/08_tracking/bug/native_llm_caret_smux_owner_spawned_as_interpreter_of_itself_2026-11-14.md` and `doc/08_tracking/bug/caret_smux_multi_launch_spec_marker_matched_pty_echo_2026-11-14.md`.

**Final recommendation:** first establish true session↔provider↔pane binding and the missing native owner path; then extend the existing Simple IDE plugin workbench with a high-information Caret roster, reliable keyboard switching, evidence-based attention and the existing Slop trace viewer. This gets a better daily multi-agent terminal **and** an evidence-aware software engineering IDE without duplicating smux, graph, test or process owners.
