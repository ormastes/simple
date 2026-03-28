# Design Skill (Codex) -- Step 4: Architecture + System Test Design

**Pipeline:** Step 4 of 5 (after design_gemini, before design_claude)

## Prerequisites
- UI designs from Step 3
- Requirements from `doc/02_requirements/feature/` and `doc/02_requirements/nfr/`

## Phase 1: Architecture Design

1. Spawn agents for architecture creation
2. Evaluate architecture patterns (ask user which to use)
3. Apply MDSOC architecture pattern (reference `src/compiler/85.mdsoc/`)
4. Document architecture decisions

### Output
- `doc/04_architecture/<feature>.md`

## Phase 2: System Test Design

1. Generate system test base using SSpec framework (see `/sspec`)
2. Built-in matchers only: `to_equal`, `to_be`, `to_be_nil`, `to_contain`, `to_start_with`, `to_end_with`, `to_be_greater_than`, `to_be_less_than`
3. Create tests at `doc/06_spec/app/<app_name>/feature/<feature>_spec.spl`
4. System test suite coverage check for each test suite against requirements
5. Each REQ-NNN must have at least one `it` block

### Output
- `doc/03_plan/sys_test/<feature>.md`
- SSpec test files in `doc/06_spec/`

## Handoff
Pass architecture + tests to `/design_claude` (Step 5).
