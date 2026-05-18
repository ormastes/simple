# SStack State: executable-size-reduction

## User Request
> next task from the plan — executable_size_reduction (9 tasks: symbol roots, size budget, strip/packaging, crate split, dependency audit)

## Task Type
feature

## Refined Goal
> Implement executable size reduction infrastructure: runtime symbol root registry, size budget tracker, dependency closure audit, binary size tracking, release strip scaffolding, and verification specs.

## Acceptance Criteria
- [ ] AC-1: Runtime symbol root registry — explicit root list replacing whole-archive, with root discovery queries
- [ ] AC-2: Root calculation coverage — root discovery validation and conflict detection
- [ ] AC-3: Size budget tracker — per-binary size budgets with pass/fail/warning thresholds
- [ ] AC-4: Release strip scaffolding — strip config, debug symbol policy, size-before/after reporting
- [ ] AC-5: Runtime ABI surface — dedicated ABI boundary definition separating runtime from loader
- [ ] AC-6: Loader dependency audit — closure analysis with unused/redundant detection
- [ ] AC-7: Per-binary dependency audit — CLI, bootstrap, native-built package dependency maps
- [ ] AC-8: Architecture split scaffolding — dependency edge removal plan with safe/blocked classification
- [ ] AC-9: Size tracking report — before/after comparison, regression detection, CI integration contract
- [ ] AC-10: Verification spec — 20 tests covering roots, budget, audit, strip, tracking

## Phase Checklist
- [x] 1-dev (Developer Lead) — 2026-05-18
- [x] 2-4 — skipped (plan doc comprehensive)
- [ ] 5-implement (Engineer)
- [ ] 6-refactor (Tech Lead)
- [ ] 7-verify (QA)
- [ ] 8-ship (Release Mgr)

## Phase Outputs

### 1-dev
10 ACs across 9 plan tasks. 5 parallel agents (A-E). Existing: executable-size-bloat-analysis spipe (empty state).

### 5-implement
<pending>
