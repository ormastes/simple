# Caret Workbench UI Feature Expert

## Role

Maintain feature-specific process knowledge for the Caret Suite 1.0 workbench UI, IDE extensions, smux integration and traceability program. Use this skill when work touches `src/app/llm_caret/`, the IDE extension host, smux pane binding or the trace view. Status 2026-11-14: a proposed plan; nothing is release-qualified.

## What it is

Caret is a specialized profile of Simple IDE, not a new IDE. smux is the single terminal multiplexer: native provider CLIs run as real PTY children there; all other panels are native Simple TUI/GUI views. Identity (session, provider, pane, worktree, generation) comes before cosmetics; observation is evidence-based with confidence; traceability reuses `simple trace` and Slop and never shows structural-only results as verified.

## The four docs

- Research (plan 1, 2, 16, with 2026-11-14 re-verification): [caret_workbench_ui_research_2026-11-14.md](../../01_research/app/llm_caret/caret_workbench_ui_research_2026-11-14.md)
- Design (plan 3-11, 15): [caret_workbench_ui.md](../../05_design/app/llm_caret/caret_workbench_ui.md)
- Requirements (stable IDs): [caret_workbench_ui.md](../../02_requirements/app/llm_caret/caret_workbench_ui.md)
- Plan (phases P0-P8, CU-001..CU-020, backlog, lane status): [caret_workbench_ui_plan.md](../../03_plan/app/llm_caret/caret_workbench_ui_plan.md)

## Owner map (condensed from design section 10)

| Owner | Owns | Must not own |
|---|---|---|
| `src/os/apps/smux` | panes, capture, leases, input | agent semantics, trace graph |
| `std.sosix` / host daemon | PTY, heartbeats, auth | UI layout, prompt grammar |
| `src/app/llm_caret/workbench` | session projection, binding, view state | agent execution |
| `src/app/llm_caret/observer/` (proposed) | observations, confidence, stall | input, approval authority |
| `src/lib/editor/extensions` | manifest v2, registries | domain databases |
| `src/app/ide`, `src/app/editor` | profile parity, key router | provider side effects |
| `src/app/traceability`, `std.common.traceability` | graph, qualification, queries | GUI selection |
| `src/app/slop` | trace widgets | duplicate indexing |

## Requirement ID families

`REQ-CARET-UI-*` (binding, input safety, cell writer, leader key), `REQ-CARET-EXT-*` (manifest v2, v1 compat, TUI profile parity, deactivation), `REQ-CARET-OBS-*` (state axes, stall table, attention inbox), `REQ-CARET-TRC-*` (evidence badges, structural banner, query parity), `REQ-CARET-NFR-*`.

## Landmines (plan section 1.2)

- Native smux owner bug (open, P2): native Caret runs itself as the interpreter of `smux_client.spl`; see `doc/08_tracking/bug/native_llm_caret_smux_owner_spawned_as_interpreter_of_itself_2026-11-14.md`.
- Terminal-state specs must wait for a child-computed marker, not text the PTY echoes (`doc/08_tracking/bug/caret_smux_multi_launch_spec_marker_matched_pty_echo_2026-11-14.md`).
- Slop is a real source slice but native display and graph performance are unqualified.
- `workbench/gui_page.spl` keeps an `Option<SessionView>` compiler workaround; remove only with a regression test once the compiler bug is fixed.
- Fixed in waves 1-3 (2026-11-15): real provider/generation in `session_source`, cell-aware `_put_str`, `ide --tui --profile`, smux owner argv. Still open: `cs` publishes generation 1 only (no restart detection); `bridge_worker` observer log is process-local; editor `view.show` passes no trace snapshot; `Ctrl+B` belongs to smux.
- CU-017 GUI (2026-11-15): DPI scale is integer permille (1000 = 1x, as in `std.ui.layout`); `gui_layout.workbench_mode_for_scaled_width` divides device px by the scale before the breakpoints; `gui_page.render_workbench_page_scaled` emits `data-scale-permille` + `--ui-scale`; `gui.caret_gui_html_for_path` reads `?w=&scale=` and `main._gui_http_handle` serves it. Accessible role/name per widget lives in `workbench/gui_a11y.spl` (`a11y_attrs` is the only way `gui_page` writes role/aria-label; footer is `role=status aria-live=polite`). Spec: `test/01_unit/app/llm_caret/workbench/gui_dpi_a11y_spec.spl`. Still unverified: real high-DPI capture and a real screen reader.
- Seams to reuse: `workbench/key_chunker.spl` (terminal passthrough), `workbench/roster_order.spl`, `workbench/capability_checklist.spl` (`/capabilities`), `observer/observer_log.spl` + `session_status.spl`, `app/editor/trace_view_host.spl`, `app/bug_resolve/close_gate.spl`, `app/bug/workaround_revert.spl`.
- Provider loaded-skill reporting (CU-020, partial): `provider_adapters.claude_loaded_skill` reads the Claude `PreToolUse` Skill-tool payload; `hook_bridge.drain_hook_events` -> `observer_log.observer_record_skill`; surfaced by `session_status.session_loaded_skills_text` (TUI status line) and the `/capabilities` Skills row. SessionStart carries no skills; Codex reports none. First-use hints (`observer/skill_hint.spl`, `session_status.session_skill_hint_text`, TUI status line) show for the first 3 uses per session/skill then decay. `provider_adapters` maps Claude PostToolUse/PostToolUseFailure to JobHeartbeat. `app.editor.profile_plan.profile_sync_context` (called each frame by TUI/GUI shell loops) is the production caller of `set_context_keys`, fed by `session_source.live_focus` (published by `cs_main`) and the selected session provider.
- Provider loaded-skill reporting (CU-020, partial): `provider_adapters.claude_loaded_skill` reads the Claude `PreToolUse` Skill-tool payload; `hook_bridge.drain_hook_events` -> `observer_log.observer_record_skill`; surfaced by `session_status.session_loaded_skills_text` (TUI status line) and the `/capabilities` Skills row. SessionStart carries no skills. Codex: `codex_loaded_skill` reads a PreToolUse shell command that reads `skills/<name>/SKILL.md`, `codex_requested_skills` reads `$name` tokens in a UserPromptSubmit prompt (both recorded by `observer_record_skill`, independent of lifecycle acceptance); the Skills row diffs "requested but not loaded". Payload shapes are assumed from Codex hook docs, not captured from a live Codex run. First-use hint decay is not built.
- Adding a `use app.<dir>` from compiler-reachable code requires listing `<dir>` in `scripts/bootstrap/stage2-build-input-app-dirs.txt` (required gate).

## Update Rule

After research, requirements, design, implementation, verification, or release work changes this feature, refresh the links and lane status here and in the plan doc. CU-001..CU-020 status lives in the plan doc ("Acceptance CU-001..CU-020"). Lane PRs: wave 1 #9200-#9221, wave 2 #9233/#9234/#9237/#9242/#9243/#9287, wave 3 #9294/#9295/#9301/#9313/#9315/#9317.

Template: [feature_skill.md](../../template/feature_skill.md)

## Fleet transport (CU-001/CU-010, interpreter-verified only)

`workbench/fleet_transport.spl` is the multi-host seam: a peer exports its LOCAL
roster as a `v1` TAB-separated wire (`export_fleet_snapshot`, written each
frame when `LLM_CARET_FLEET_EXPORT` is set); this host polls each declared host
by running its transport command through `process_run_bounded`
(`LLM_CARET_FLEET_HOSTS=id=ssh-target:path,id=local:path`; `local` = `cat path`
loopback). Rows are namespaced `<host>/<id>`, labelled `<host>:<id>`; an
unreachable host keeps its last rows as `Transport.Disconnected` +
`ProcessLifecycle.Lost`. Production caller: `pane_team.publish_pane_team` ->
`publish_fleet_sessions`. Spec: `test/01_unit/app/llm_caret/workbench/fleet_transport_spec.spl`.
Fleet gaps closed (`fleet_gaps_spec`, 6/6, loopback + interpreter): bounded
exponential reconnect backoff per host (`min(2^n,16)` polls, back to connected on
first success; `fleet_host_state`); input forwarding `fleet_send` (host send
command + `<id> <line>` appended; wired in `pane_team.send_to_agent`, which
`main.spl` `--send` calls); credential-safe host panel row (`fleet_host_panel_rows`:
id + kind + state, drawn by `tui_view._render_roster`); 50 agents/5 loopback
hosts with attention-first grouping (`session_source._attention_first`); all
lifecycle states carried over the wire.
Remaining gaps: no real ssh run; ssh hosts have no send command (loopback only,
`<snapshot>.in` inbox); snapshot polling not push; the GUI page does not draw the
host row; the 50-row roster is clipped by the TUI region height (attention rows
come first); the other CU-010 states are carried, not re-verified natively.

## CU-001..020 traceability (2026-11-17)
Owner plan copied to `doc/03_plan/app/llm_caret/caret_suite_final_ui_extension_traceability_plan.md`;
per-row status in `doc/03_plan/app/llm_caret/caret_suite_cu_verification_status.md`.
Tagged specs exist for 17/20 rows; CU-007, CU-012, CU-018 have none. Native
verification is PENDING for all rows (bootstrap in progress) — never mark PASS
without native evidence.
