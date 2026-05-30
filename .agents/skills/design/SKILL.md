---
name: design
description: Create architecture, UI design, system tests, and detail design for a feature. Self-sufficient — if research/requirements missing, does them first. Does not depend on any other LLM.
---

# Design — Self-Sufficient

**Self-sufficient.** If research/requirements missing, do them first.

## Prerequisites Check

| Artifact | Path | If missing |
|----------|------|-----------|
| Requirements | `doc/02_requirements/feature/<feature>.md` | Run $research first |
| NFR | `doc/02_requirements/nfr/<feature>.md` | Run $research first |

## Phase 1: UI Design (if applicable)

- TUI: `doc/05_design/<feature>_tui.md`
- GUI: `doc/05_design/<feature>_gui.md`
- Capture plan for UI-facing specs:
  - TUI captures: `build/test-artifacts/<spec-relative-path>/`
  - GUI screenshots/goldens/diffs: `doc/06_spec/image/<spec-relative-path>/`
  - Generated SSPEC docs embed these through `**Screenshots:**` or
    `**TUI Captures:**` metadata.

## Phase 2: Architecture

- Evaluate patterns, apply MDSOC where appropriate
- Output: `doc/04_architecture/<feature>.md`

## Phase 3: System Test Design

- SPipe BDD tests: `doc/06_spec/app/<app_name>/feature/<feature>_spec.spl`
- Test plan: `doc/03_plan/sys_test/<feature>.md`
- Matchers (built-in only): `to_equal`, `to_be`, `to_be_nil`, `to_contain`, `to_start_with`, `to_end_with`, `to_be_greater_than`, `to_be_less_than`
- Every REQ-NNN must have at least one test
- Scenario-oriented specs must generate docs that read like hand-written
  manuals: primary flows visible, setup expanded through `@prev`/`@inline`,
  executable SPipe folded, and advanced/edge/matrix/stress details folded or
  skipped by policy.
- TUI/GUI behavior must include visible-state capture evidence when practical.
- Environmental specs should capture meaningful typed evidence (`api`,
  `protocol`, `exec`, `binary`, `text`, `log`, or `artifact`) when screenshots
  are not the right evidence.

## Phase 4: Detail Design

- Data structures, algorithms, module interactions, error handling
- Output: `doc/05_design/<feature>.md`
- Agent tasks: `doc/03_plan/agent_tasks/<feature>.md`

## Phase 5: Quality Check

- Verify SPipe quality (A grade, real assertions, edge cases)
- Generate/read mirrored `doc/06_spec/...` for scenario-oriented specs and
  update steps/captures/visibility until the manual is usable without opening
  the source test.
- Ask user if architecture/design needs changes

## Rules

- If requirements missing, do research first
- If another LLM already created artifacts, review and extend — never overwrite
- Every REQ-NNN must have test coverage
