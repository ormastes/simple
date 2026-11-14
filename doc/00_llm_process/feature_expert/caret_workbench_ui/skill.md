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
- Also: `session_source.spl` hardcodes provider `"process"`; `pane_source.spl` pane may not be the manager's child; `tui_view.spl` `_put_str` slices bytes; `ide --tui` ignores `--profile`; `Ctrl+B` belongs to smux.

## Update Rule

After research, requirements, design, implementation, verification, or release work changes this feature, refresh the links and lane status here and in the plan doc. Lane PRs at 2026-11-14: #9200 binding, #9201 ide tui profile, #9202 cell writer, #9203 observer core.

Template: [feature_skill.md](../../template/feature_skill.md)
