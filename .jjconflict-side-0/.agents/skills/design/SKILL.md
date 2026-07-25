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

- SPipe BDD tests: `test/03_system/app/<app_name>/feature/<feature>_spec.spl`
- Generated/manual SPipe docs: `doc/06_spec/03_system/app/<app_name>/feature/<feature>_spec.md`
- Never create executable `.spl` specs under `doc/06_spec`; verify
  `find doc/06_spec -name '*_spec.spl' | wc -l` is `0`.
- Test plan: `doc/03_plan/sys_test/<feature>.md`
- Matchers (built-in only): `to_equal`, `to_be`, `to_be_nil`, `to_contain`, `to_start_with`, `to_end_with`, `to_be_greater_than`, `to_be_less_than`
- Every REQ-NNN must have at least one test
- Before lower-model sidecars fan out, define shared interface names,
  manual-facing `step("...")` flow helper names, and setup/checker helper
  names. Temporary placeholder helpers must fail explicitly (`assert(false)` or
  equivalent), not pass silently.
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
- Agent tasks: `doc/03_plan/agent_tasks/<feature>.md` with sidecar lanes/`N/A`, merge owner, and final reviewer
- Agent-task docs for broad lanes must list lower-model sidecar lanes or `N/A`,
  such as Codex Spark, Claude Haiku, or Claude Sonnet for parallel exploration,
  plus merge owner and final best available normal/highest-capability reviewer.
  Before those sidecars start, the primary/best-model pass defines the shared
  interface names, manual `step("...")` flow helper names, setup/checker helper
  names, and placeholder fail-fast helpers (`assert(false)` or `fail(...)`) that
  sidecars must target.
- The final best available normal/highest-capability reviewer must accept the
  merged sidecar design and generated-manual quality before implementation
  handoff.

## Phase 5: Quality Check

- Verify SPipe quality (A grade, real assertions, edge cases)
- Generate/read mirrored `doc/06_spec/...` for scenario-oriented specs and
  update steps/captures/visibility until the manual is usable without opening
  the source test.
- If design changes workflow/tooling, evidence wrappers, generated spec shape,
  or verification contracts, update matching `doc/07_guide`, `doc/06_spec`,
  `.codex/skills/`, `.agents/skills/`, `.claude/skills/`,
  `.claude/agents/spipe/`, and `.gemini/commands/` instructions before implementation handoff.
- Ask user if architecture/design needs changes

## Rules

- If requirements missing, do research first
- If another LLM already created artifacts, review and extend — never overwrite
- Every REQ-NNN must have test coverage
