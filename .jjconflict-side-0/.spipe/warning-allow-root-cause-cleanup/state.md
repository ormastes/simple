# Warning/Allow Root-Cause Cleanup

## Status: CLOSED — 2026-05-20

## Phases
- [x] 1-dev (Developer Lead) — 2026-05-18
- [~] 2-research (skipped)
- [~] 3-arch (skipped)
- [~] 4-spec (skipped)
- [x] 5-implement — 2026-05-18
- [x] 6-refactor — 2026-05-18
- [x] 7-verify — 2026-05-18
- [x] 8-ship — 2026-05-18

## Task Type
feature

## Refined Goal
Repair Rust strict workflow pathing, add targeted Simple strict-lint workflow,
fix current Rust strict-gate blockers, keep decorator whitelist aligned with
stdlib decorators, add regression canaries.

## Tasks
- Task A: repair Rust strict workflow pathing and preserve its strict Clippy command.
- Task B: add the targeted Simple strict-lint workflow.
- Task C: fix current Rust strict-gate blockers in primitive-sort runtime/bench code.
- Task D: keep the decorator whitelist aligned with stdlib decorators used by the repo.
- Task E: add regression canaries and document the remaining deferred debt.

## Phase Outputs

### 5-implement
Source files created:
- `.spipe/warning-allow-root-cause-cleanup/decorator_whitelist.spl`
- `.spipe/warning-allow-root-cause-cleanup/attribute_whitelist.spl`
- `.spipe/warning-allow-root-cause-cleanup/strict_lint_lane.spl`
- `.spipe/warning-allow-root-cause-cleanup/regression_canary.spl`
Spec file:
- `.spipe/warning-allow-root-cause-cleanup/warning_allow_cleanup_spec.spl`

### 7-verify
All 20 tests pass.
