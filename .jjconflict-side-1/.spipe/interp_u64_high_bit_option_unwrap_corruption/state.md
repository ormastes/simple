# Feature: interp-u64-high-bit-option-unwrap-corruption

## Raw Request
Fix canonical P1 BugDB row `interp_u64_high_bit_option_unwrap_corruption` only; reproduce it, fix the first pure-Simple owner, add exact and adjacent regressions, and update expert knowledge.

## Task Type
bug

## Refined Goal
Preserve the full `u64` value domain when a struct crosses a pure-Simple optional return and `if val` unwrap boundary, including values at and above `2^63`.

## Acceptance Criteria
- AC-1: Claim the canonical BugDB row before source edits and retain the claim in its investigation log.
- AC-2: Reproduce the exact `2^63` failure once and retain the pre-fix result.
- AC-3: Trace the pure-Simple optional return and unwrap path before considering Rust/runtime changes, then fix the first faulty owner without a checksum-width workaround.
- AC-4: Add an exact regression for `2^63` and adjacent regressions for `2^63 - 1`, `2^63 + 1`, and `u64::MAX` through the same Option-of-struct boundary.
- AC-5: Focused tests pass and the BugDB row is updated only to the evidence-supported status.
- AC-6: Refresh the applicable feature- and layer-expert skills; update the bug report with ownership and evidence. Other architecture/design/guide docs are N/A because this is a semantic correctness repair with no surface or workflow change. Any newly discovered gap is tracked in BugDB.

## Scope Exclusions
Rendering policy changes, checksum masking changes, unrelated interpreter defects, and Rust/runtime edits without proof that the pure-Simple layer delegates correctly.

## Cooperative Review
N/A: this is one narrow canonical bug row with one source owner and focused boundary tests.

## Phase
implementation-handoff

## Log
- dev: Created state file with 6 acceptance criteria (type: bug).
- implementation: Fixed unsigned relational ordering at the Rust tree-interpreter owner; focused owner tests pass 2/2 and a rebuilt diagnostic probe crosses the exact Option-of-struct boundary.
- verification: Language-level SSpec is retained but production execution is pending an admitted Stage 4 runner; the Rust runner currently stops first on the unrelated `verification_semantic_coverage.spl` parse defect.
