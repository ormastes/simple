# Feature: doc-coverage-missing-modules

## Raw Request
fix all remain bug and feature request and abandon plans.. and in mind pure simple is main rust is just seed. use skill $sp_dev

Trackers:
- doc/08_tracking/bug/doc_coverage_markdown_generator_module_missing_2026-05-30.md
- doc/08_tracking/bug/doc_coverage_sdoctest_analysis_module_missing_2026-05-30.md

## Task Type
bug

## Refined Goal
Provide the missing pure Simple `app.doc_coverage` modules and import paths required by the doc coverage markdown and SDoctest analysis specs.

## Acceptance Criteria
- AC-1: `test/01_unit/app/doc_coverage/markdown_report_spec.spl` resolves all doc coverage imports and passes without weakening assertions.
- AC-2: `test/01_unit/app/doc_coverage/sdoctest_coverage_spec.spl` resolves all doc coverage imports and passes without weakening assertions.
- AC-3: The implementation lives under `src/app/doc_coverage/**` as Simple source, not SMF-only or Rust-only behavior.
- AC-4: Both bug trackers are updated to resolved with focused verification commands.

## Scope Exclusions
Full doc coverage CLI/system behavior is outside this slice unless required by the two missing-module specs.

## Phase
verified

## Log
- dev: Created state file with 4 acceptance criteria (type: bug).
- implement: Added pure Simple doc coverage types, markdown reporting, SDoctest analysis, and module re-exports under `src/app/doc_coverage/`.
- implement: Corrected markdown report spec imports to the `app.doc_coverage` namespace.
- verify: `SIMPLE_LIB=/tmp/simple-macro-intro-sync/src /home/ormastes/dev/pub/simple/src/compiler_rust/target/debug/simple check src/app/doc_coverage/types/doc_item.spl src/app/doc_coverage/types/coverage_result.spl src/app/doc_coverage/analysis/sdoctest_coverage.spl src/app/doc_coverage/reporting/markdown_generator.spl test/01_unit/app/doc_coverage/sdoctest_coverage_spec.spl test/01_unit/app/doc_coverage/markdown_report_spec.spl` passed.
- verify: `SIMPLE_LIB=/tmp/simple-macro-intro-sync/src /home/ormastes/dev/pub/simple/src/compiler_rust/target/debug/simple run test/01_unit/app/doc_coverage/sdoctest_coverage_spec.spl` passed 12 examples.
- verify: `SIMPLE_LIB=/tmp/simple-macro-intro-sync/src /home/ormastes/dev/pub/simple/src/compiler_rust/target/debug/simple run test/01_unit/app/doc_coverage/markdown_report_spec.spl` passed all report groups.
