# SSpec Count Truthfulness — Lane State

## Raw request

Add modern fail-closed, step-based SSpec system coverage for the completed
count-truthfulness implementation lane, with positive/edge/error assertions,
REQ traceability, a Markdown-only manual mirror, lane process documentation,
and honest runtime blocking when no admitted pure-Simple CLI exists.

## Acceptance criteria

- [x] One executable system spec lives under `test/03_system/infra/` and uses
  the frozen visible `step("...")` vocabulary.
- [x] Positive, anchored edge, runner-error, and missing-identity scenarios
  use built-in matchers with no placeholder passes.
- [x] `REQ-SCT-001` through `REQ-SCT-003` have positive/edge/error traceability.
- [x] The Markdown-only mirror, test plan, guide, feature-expert skill, and LLM
  wiki are synchronized with the executable contract.
- [x] No shared global skill is modified and no executable spec is placed
  under `doc/06_spec`.
- [ ] Runtime, docgen, and `sspec-maintain` evidence: **TEST_BLOCKED** until a
  current-source admitted pure-Simple CLI is available.

## Phase

`system-test-authored-runtime-blocked`

## Status

**TEST_BLOCKED — 2026-08-16.** The implementation criterion is complete and
modern step-based system coverage is authored for automatic execution, but this
worktree has no current-source admitted pure-Simple CLI. The Rust bootstrap seed
is forbidden and no stale or unqualified binary may provide PASS evidence.

## Scope

Fail-closed coverage for the SSpec count-truthfulness gate. The lane proves that
the gate admits only a qualified self-hosted runner, preserves a failing runner's
nonzero status, and accepts a result only when the statically declared and
runner-reported example counts agree.

## Requirements

- `REQ-SCT-001`: admit the selected runner's pure-Simple identity before any
  count measurement.
- `REQ-SCT-002`: preserve a nonzero SSpec runner result; never convert it to a
  passing count claim.
- `REQ-SCT-003`: require exact equality between anchored declared examples and
  the runner's reported total.

## Frozen executable interface

- Helper: `run_count_truthfulness_guard`
- Visible flow:
  1. `Select the admitted pure-Simple SSpec runner`
  2. `Run the count-truthfulness gate on a two-example passing spec`
  3. `Confirm declared and reported counts agree`
  4. `Run the count-truthfulness gate on the anchored-count edge fixture`
  5. `Confirm non-example text does not inflate the declared count`
  6. `Run the count-truthfulness gate on a deliberately failing spec`
  7. `Confirm the runner failure remains nonzero`
  8. `Run the count-truthfulness gate with a missing compiler path`
  9. `Confirm unavailable identity is TEST_BLOCKED and never PASS`

## Artifacts

- [Executable system spec](../../test/03_system/infra/sspec_count_truthfulness_spec.spl)
- [Mirrored Markdown manual](../../doc/06_spec/03_system/infra/sspec_count_truthfulness_spec.md)
- [System test plan](../../doc/03_plan/sys_test/sspec_count_truthfulness.md)
- [Operator guide](../../doc/07_guide/infra/sspec_scenario_manual.md)
- [Feature-expert skill](../../doc/00_llm_process/feature_expert/modern_sspec/skill.md)
- [LLM wiki](../../doc/00_llm_process/llm_wiki.md)
- [Tracking TODO](../../doc/08_tracking/todo/check_scripts_seed_identity_fail_open_2026-07-28.md)
- [Implementation gate](../../scripts/check/check-sspec-count-truthful.shs)

## Evidence state and resume rule

- Static quality and repository guard results belong in the system test plan.
- Runtime, `spipe-docgen`, and `sspec-maintain` were not run in this lane state:
  no admitted current-source pure-Simple CLI is available.
- Resume only after the selected CLI passes canonical self-hosted admission.
  Then execute the spec, regenerate its mirror, run `sspec-maintain`, and retain
  the exact binary identity and command outcome. Any missing identity, nonzero
  runner result, missing summary, or count mismatch remains non-PASS.
- Never substitute the Rust seed, a stale deployed artifact, a handwritten
  success claim, or a skipped execution for qualified runtime evidence.

## Log

- system-test: Added the four-scenario executable contract and three immutable,
  non-discovered fixtures with frozen visible steps and REQ traceability.
- manual: Added a Markdown-only authored mirror and test plan; both state
  `TEST_BLOCKED` and do not claim docgen provenance.
- process-docs: Updated the scenario guide, lane feature-expert skill, and LLM
  wiki without modifying a shared global skill.
- runtime: Not run. No current-source admitted pure-Simple CLI is available.
