# Design Skill — Architecture, UI, System Tests, Detail Design

## Cooperative Phase
**Step 5 of 5** in multi-LLM cooperative pipeline.
- Solo mode: Full design (UI + architecture + system tests + detail)
- Cooperative mode: Receives artifacts from Gemini `/design` (Step 3) and Codex `$design` (Step 4), then refines SSpec quality + detail design
- See: `doc/guide/llm_cooperative_dev_phase.md`

**Self-sufficient.** If research/requirements are missing, do `/research` first (or do it inline).

## Prerequisites Check

Before starting, verify these exist — if missing, create them:

| Artifact | Path | If missing |
|----------|------|-----------|
| Requirements | `doc/02_requirements/feature/<feature>.md` | Run research + ask user to select |
| NFR | `doc/02_requirements/nfr/<feature>.md` | Run research + ask user to select |

## Phase 1: UI Design (if feature has UI)

1. TUI mockups (box-drawing, ANSI colors): `doc/05_design/<feature>_tui.md`
2. GUI mockups (web patterns, responsive): `doc/05_design/<feature>_gui.md`
3. Present component lists to user for confirmation

Skip if feature has no UI component.

## Phase 2: Architecture

1. Evaluate architecture patterns (ask user which to use)
2. Apply MDSOC pattern where appropriate (see `src/compiler/85.mdsoc/`)
3. Output: `doc/04_architecture/<feature>.md`

## Phase 3: System Test Design

1. Generate SSpec BDD tests: `doc/06_spec/app/<app_name>/feature/<feature>_spec.spl`
2. Follow SSpec rules:
   - `describe`, `it`, `expect` built-in (no import)
   - One assertion concept per test
   - Clear names: `it "adds two positive numbers":` not `it "works":`
   - `"""..."""` docstrings for generated docs
3. Matchers (built-in only): `to_equal`, `to_be`, `to_be_nil`, `to_contain`, `to_start_with`, `to_end_with`, `to_be_greater_than`, `to_be_less_than`
4. Verify every REQ-NNN has at least one test
5. Test plan: `doc/03_plan/sys_test/<feature>.md`

## Phase 4: Detail Design

1. Create detailed design: data structures, algorithms, module interactions, error handling
2. Output: `doc/05_design/<feature>.md`
3. Agent task breakdown: `doc/03_plan/agent_tasks/<feature>.md`

## Phase 5: Quality Check

1. Verify SSpec quality (target: A grade) — real assertions, edge cases, full REQ coverage
2. Ask user: "Should architecture or design change?"
3. If yes, loop back to relevant phase

## Outputs

| Artifact | Location |
|----------|----------|
| UI design (TUI) | `doc/05_design/<feature>_tui.md` |
| UI design (GUI) | `doc/05_design/<feature>_gui.md` |
| Architecture | `doc/04_architecture/<feature>.md` |
| System tests | `doc/06_spec/app/<app_name>/feature/<feature>_spec.spl` |
| Test plan | `doc/03_plan/sys_test/<feature>.md` |
| Detail design | `doc/05_design/<feature>.md` |
| Agent tasks | `doc/03_plan/agent_tasks/<feature>.md` |

## Critical Rules

- If requirements missing, do research first — never design without requirements
- If another LLM already created artifacts, review and extend — never overwrite
- Every REQ-NNN must have test coverage
- User must approve architecture before detail design
