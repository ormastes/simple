# Feature: compiled-check-signature-parser

## Raw Request
Fix lane C from compiled-check routing commit ca2cbf7fe495: type/multiline signature category (62 individually failing files).

## Task Type
bug

## Refined Goal
Make the pure-Simple compiled checker accept canonical type and multiline function signatures with parity to the authoritative parser without weakening invalid-syntax diagnostics.

## Acceptance Criteria
- AC-1: Focused exact reproductions for the routed type/signature surfaces pass through the authoritative parser and the repaired pure-Simple parser.
- AC-2: Adjacent valid type/signature syntax passes and an adjacent invalid signature remains rejected.
- AC-3: The shared parser/checker root is fixed without editing routed application/library sources or out-of-scope generic parser, concurrency-lint, and bootstrap-authority files.
- AC-4: The immutable 62-file routed subset is rerun once against the repaired checker and its result is recorded.
- AC-5: The aggregate bug entry records the lane owner, branch, evidence, and status.

## Scope Exclusions
Generic parser, concurrency lint, bootstrap authority, and unrelated parser/source categories.

## Cooperative Review
N/A: this is one bounded parser category with a single shared owner and a hard three-cycle verification cap.

## Phase
dev-done

## Log
- dev: Created state file with 5 acceptance criteria (type: bug).
- implement: Added semantic flat-tag preservation for `mut T` and canonical `[]` parsing with exact, adjacent-valid, and adjacent-invalid fixtures.
- verify: Fresh checker `563f5d66a8fb` clears 19 routed initial diagnostics; 14 complete files pass and 5 expose unrelated later diagnostics.
- verify: Nested multiline method signatures remain open after the three-cycle cap; owner narrowed to the class-method parser.
