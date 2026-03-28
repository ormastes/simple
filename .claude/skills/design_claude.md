# Design Skill (Claude) -- Step 5: SSpec Quality + Detail Design

**Pipeline:** Step 5 of 5 (final design step, before `/impl`)

## Prerequisites
- Architecture from Step 4 (`doc/04_architecture/<feature>.md`)
- System tests from Step 4 (SSpec files)
- Requirements from Step 2 (`doc/02_requirements/feature/`)

## Phase 1: SSpec Quality Verification

1. Read generated SSpec system tests from Step 4
2. Verify doc quality (target: **A grade**)
3. Check: real assertions (not pass_todo), edge cases, requirement coverage
4. Update and regenerate until A grade achieved
5. Verify system test doc fully describes feature

## Phase 2: Fill Missing Parts

1. Identify missing/dummy parts in system tests
2. Add edge case system SSpec tests
3. Ensure all REQ-NNN from requirements have test coverage
4. Fill up any dummy parts with real assertions

## Phase 3: Detail Design + Agent Tasks

1. Create detailed design: data structures, algorithms, module interactions, error handling
2. Create agent task breakdown
3. Assign difficulty levels (1-5) per task

### Output
- `doc/05_design/<feature>.md` (detail design)
- `doc/03_plan/agent_tasks/<feature>.md` (task breakdown)

## Phase 4: Architecture/Design Review

Ask user: **"Should architecture or design change?"**
- If yes -> loop back to relevant step
- If no -> proceed to implementation

## Phase 5: Transition to Implementation

- Research and design phases are now complete
- See `/impl` skill for implementation workflow
- After all impl: run `/refactor` skill
- Run `/verify` by Claude for production readiness
- Add/update guide documents in `doc/07_guide/` if needed
