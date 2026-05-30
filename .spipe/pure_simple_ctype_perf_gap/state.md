# Feature: pure-simple-ctype-perf-gap

## Raw Request
Work in /home/ormastes/dev/pub/simple on tracker doc/08_tracking/bug/pure_simple_ctype_perf_gap_2026-05-18.md. You are not alone in the codebase: do not revert others' edits. Own only ctype/perf-related pure Simple files, focused tests/bench docs, .spipe/pure_simple_ctype_perf_gap/**, and tracker. Use $sp_dev workflow. Do not add Rust as solution; pure Simple is main. Implement next concrete mitigation or produce verification evidence and update tracker. Report changed paths, tests/benchmarks, blockers.

## Task Type
bug

## Refined Goal
Determine whether a remaining pure-Simple ctype performance mitigation is available, implement it if concrete, or produce focused verification evidence that the current pure-Simple path is exhausted and update the tracker.

## Acceptance Criteria
- AC-1: The ctype/perf tracker records the latest focused verification result with exact commands and observed native/C ratios or pass/fail status.
- AC-2: Any changed implementation stays within ctype/perf-related pure Simple files, focused tests/bench docs, `.spipe/pure_simple_ctype_perf_gap/**`, and the tracker.
- AC-3: No Rust implementation is added as the solution for this pass.
- AC-4: Focused ctype checks and benchmarks are run, or any failure to run them is recorded with the concrete blocker.
- AC-5: If no shippable pure-Simple mitigation remains, the tracker states that conclusion with current evidence instead of changing the library speculatively.

## Scope Exclusions
- Rust backend/codegen/LTO changes.
- Unrelated library, compiler, documentation, or benchmark changes.
- Reverting other contributors' edits.

## Phase
dev-done

## Log
- dev: Created state file with 5 acceptance criteria (type: bug).
