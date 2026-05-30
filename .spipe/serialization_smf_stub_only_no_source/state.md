# Feature: serialization-smf-stub-only-no-source

## Raw Request
Work in /home/ormastes/dev/pub/simple on tracker doc/08_tracking/bug/serialization_smf_stub_only_no_spl_source_2026-05-30.md. You are not alone in the codebase: do not revert others' edits. Keep write scope to src/lib/common/serialization/**, test/unit/lib/common/serialization_extended_spec.spl only if needed, .spipe/serialization_smf_stub_only_no_source/**, and the tracker. Use $sp_dev workflow. Pure Simple is the main implementation path; Rust is only seed/tooling. Implement source restoration, run focused serialization tests, update tracker. Report changed paths, tests, blockers.

## Task Type
bug

## Refined Goal
Restore Pure Simple source for `std.common.serialization` so interpreter-mode imports and the focused serialization extended spec can execute against real implementations instead of SMF placeholder stubs.

## Acceptance Criteria
- AC-1: `src/lib/common/serialization/` contains Simple source files, including an export entrypoint, for the functions exercised by `test/unit/lib/common/serialization_extended_spec.spl`.
- AC-2: `use std.common.serialization` resolves in interpreter mode without relying on placeholder `.smf` files.
- AC-3: The focused serialization test `bin/simple test test/unit/lib/common/serialization_extended_spec.spl --mode=interpreter` passes or any remaining failure is documented as an unrelated blocker.
- AC-4: New serialization implementation files contain no `pass_todo`, TODO-only bodies, or hardcoded placeholder returns.
- AC-5: `doc/08_tracking/bug/serialization_smf_stub_only_no_spl_source_2026-05-30.md` records the implementation status, test result, and any blocker.

## Scope Exclusions
- Do not edit outside `src/lib/common/serialization/**`, `test/unit/lib/common/serialization_extended_spec.spl`, `.spipe/serialization_smf_stub_only_no_source/**`, and the tracker.
- Do not rewrite Rust compiler/runtime behavior except as seed/tooling if required.
- Do not revert unrelated edits from other contributors.

## Phase
dev-done

## Log
- dev: Created state file with 5 acceptance criteria (type: bug).
