# Feature: compiler_native_capsule_symbol_sort

## Raw request

Add modern fail-closed, step-based SSpec system coverage for compiler
performance lane B, including the executable spec, mirrored Markdown manual,
system-test plan, compiler guide, lane state, and lane-owned feature-expert
wiki. Use only an admitted pure-Simple full CLI for runtime/docgen/maintenance.

## Scope owner

- Isolated worktree: `/mnt/data/worktrees/restart12-compiler_perf_lane_b_20260816`
- Branch: `codex/compiler-perf-lane-b-20260816`
- Implementation commit after linear rebase: `e4777d21a67f5bb81f9d7951d5afa226a716cf3b`
- Production owner: `src/compiler/80.driver/driver_types.spl`
- No shared `.codex/skills`, `.agents/skills`, or another lane's feature expert
  may be edited.

## Requirements

- REQ-CNSS-001: deterministic ascending order, full value retention, unchanged
  caller input.
- REQ-CNSS-002: empty, singleton, duplicate/negative, and non-power-of-two tail
  behavior.
- REQ-CNSS-003: fail-closed full-result audit with exact length/position errors.
- NFR-CNSS-001: retain measured performance evidence without a flaky SSpec
  timing threshold.

## Artifact state

- Executable SSpec:
  `test/03_system/app/compiler/feature/native_capsule_symbol_sort_spec.spl`
- Manual mirror:
  `doc/06_spec/03_system/app/compiler/feature/native_capsule_symbol_sort_spec.md`
- Test plan: `doc/03_plan/sys_test/compiler_native_capsule_symbol_sort.md`
- Guide: `doc/07_guide/compiler/check_perf.md`
- Feature expert:
  `doc/00_llm_process/feature_expert/compiler_native_capsule_symbol_sort/skill.md`
- Performance evidence:
  `doc/09_report/perf/compiler_native_capsule_symbol_sort_microbenchmark_2026-08-16.md`

## Runtime admission status

**TEST_BLOCKED (2026-08-16).** `bin/simple` is absent in the isolated
worktree. No admitted Stage 4/5 full-CLI artifact was found. The admitted
pure-Simple Stage 2 compiler with SHA-256
`56eef12f581d50aa3e400c2e358db40d3320ebfcd73e54bc150221c740c537b6`
supports only `compile` and `native-build`; it is not authority for `test`,
SPipe docgen, or `sspec-maintain`. The Rust seed and unadmitted release wrapper
were not used.

## Acceptance state

- Step-based executable scenarios: COMPLETE (9 scenarios).
- Built-in matcher-only assertions: COMPLETE.
- Positive/edge/error coverage: COMPLETE in source.
- REQ traceability: COMPLETE in spec and plan.
- Static quality: PASS — 9 scenarios, 18 visible `step("...")` calls, every
  scenario has at least two steps and one real assertion, matcher set limited
  to `to_equal` and `to_be_greater_than`, all four requirement IDs traced.
- Working direct-env guard: PASS.
- Working numbered-artifact guard: PASS.
- `doc/06_spec` executable-spec layout: PASS (zero `.spl` files).
- Working conflict-marker and exact changed-file ownership scans: PASS.
- Staged workspace-root, numbered-artifact, direct-env, diff whitespace,
  conflict-content, layout, and exact six-file ownership guards: PASS.
- Committed-range conflict tree/marker guards: PENDING until commit.
- Interpreter/native SSpec execution: TEST_BLOCKED.
- SPipe docgen and zero-stub receipt: TEST_BLOCKED.
- `sspec-maintain` score/findings receipt: TEST_BLOCKED.
- Commit/push/reachability: PENDING.

## Qualified resume sequence

After a current-source full CLI is explicitly admitted, record its resolved
path/SHA-256 and run the four commands in the system-test plan exactly once.
Any timeout, signal, zero executed examples, fallback, missing summary, stale
mirror, nonzero stub count, or blocker-capped maintenance finding is FAIL, not
a skipped pass.
