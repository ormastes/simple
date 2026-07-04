# Low Dependency UI dynSMF Selection Audit

Date: 2026-06-05

## Purpose

This audit records the accepted selection and the current implementation state.
It replaces the preselection audit and selection packet.

## Selection

- Feature: Option C, initially a thin vertical slice and now expanded in
  implementation to cover all requested default dynSMF libraries.
- NFR: NFR-A+B, static dependency gates plus runtime dynSMF evidence.
- Initial dynSMF unload/reload focus: `tui_renderer`.
- Current default dynSMF libraries: `file_io`, `net_io`, `render2d`,
  `web_renderer`, `gui_renderer`, and `tui_renderer`.

## Current Phase

`focused-implementation-verified`

Final requirements, architecture, detail design, executable specs,
implementation, generated manuals, and focused verification artifacts now
exist. Full release verification remains pending.

## Artifact Evidence

| Area | Evidence |
|------|----------|
| SPipe state | `.spipe/low-dependency-ui-dynsmf/state.md` |
| Local research | `doc/01_research/local/low_dependency_ui_dynsmf.md` |
| Domain research | `doc/01_research/domain/low_dependency_ui_dynsmf.md` |
| Feature requirements | `doc/02_requirements/feature/low_dependency_ui_dynsmf.md` |
| NFR requirements | `doc/02_requirements/nfr/low_dependency_ui_dynsmf.md` |
| Agent plan | `doc/03_plan/agent_tasks/low_dependency_ui_dynsmf.md` |
| Loader handoff | `doc/03_plan/agent_tasks/low_dependency_ui_dynsmf_loader_handoff.md` |
| Parallel work orders | `doc/03_plan/agent_tasks/low_dependency_ui_dynsmf_parallel_work_orders.md` |
| System-test plans | `doc/03_plan/sys_test/low_dependency_ui_dynsmf_dependency_gate.md`, `doc/03_plan/sys_test/low_dependency_ui_dynsmf_dynsmf_session.md` |
| Architecture | `doc/04_architecture/ui/low_dependency_ui_dynsmf.md` |
| Detail design | `doc/05_design/low_dependency_ui_dynsmf.md` |
| Feature tracking | `doc/08_tracking/feature/feature_db.sdn` row `LOW_DEPENDENCY_UI_DYNSMF_2026_06_05` |

## Acceptance Criteria Status

| AC | Status | Evidence | Remaining Work |
|----|--------|----------|----------------|
| AC-1: local and web research | Done | local/domain research docs | Keep current during implementation |
| AC-2: final requirements/NFRs | Done | final feature/NFR docs | None |
| AC-3: TUI dependency gate | Covered | dependency gate unit/system specs | Keep guards current during UI edits |
| AC-4: host adapters consume shared contracts | Covered | dependency gate and backend matrix specs | Keep adapter import checks current |
| AC-5: HTML/CSS loads only where needed | Covered | render capability spec and CSS selector checks | Keep component CSS selector evidence current |
| AC-6: dynSMF manifest entries | Covered | dynSMF unit/integration/system specs and build wrapper | Keep artifact wrapper evidence current |
| AC-7: arg/env dynSMF opt-out | Covered | dynSMF unit and startup integration specs | Keep startup policy docs current |
| AC-8: session unload/reload | Covered | system spec unloads/reloads all six default ids | Full release verification pending |
| AC-9: SPipe specs | Covered | executable specs under `test/` and generated manuals under `doc/06_spec/` | Maintain placeholder/layout guards |
| AC-10: parallel agent plan | Done | agent plan and work orders | Keep updated as code paths are assigned |

## Current Handoff Steps

1. Preserve the tracked lane paths and avoid unrelated dirty worktree files.
2. Run focused UI/dynSMF specs after touching dependency or dynSMF code.
3. Run `scripts/check/check-low-dependency-dynsmf-build-plans.shs` before
   relying on checked startup artifacts in a fresh workspace.
4. Keep generated manuals mirrored from executable specs.
5. Run full `$verify` before release; current focused report is
   `doc/09_report/verify_low_dependency_ui_dynsmf_2026-06-05.md`.
