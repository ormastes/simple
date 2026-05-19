# Import Warning Debt

## Phase
Phase 1 — Dev (defining task)

## Task Type
code-quality

## Goal
Resolve all 112 import warnings (18 compiler + 94 lib) identified in the import warning debt plan. Remove unused imports, fix duplicate imports, correct import paths, and add minimal facade modules where needed.

## Acceptance Criteria
- [ ] `bin/simple build lint` shows zero unresolved-import warnings for src/compiler
- [ ] `bin/simple build lint` shows zero unresolved-import warnings for src/lib
- [ ] No functional regressions — existing tests still pass
- [ ] Changes are .spl only (no Python/Bash)

## Status
- [x] Phase 1 (dev): Task defined
- [ ] Phase 2 (research): Warnings catalogued
- [ ] Phase 5 (implement): Warnings fixed
- [ ] Phase 7 (verify): Lint re-run clean
- [ ] Phase 8 (ship): Committed
