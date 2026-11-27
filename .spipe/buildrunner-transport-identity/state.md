# BuildRunner transport identity

## Task Type
bug

## Refined Goal
Reject worker receipts for a different immutable task before collecting outputs.

## Acceptance Criteria
- AC-1: Claim the bug and reproduce stale digest acceptance before source edits.
- AC-2: Fix the pure-Simple transport owner; retain matching task collection.
- AC-3: Cover valid output, missing output and empty failed-output regressions.
- AC-4: Update bug evidence, authored manual, BuildRunner feature wiki and
  bootstrap layer wiki; guide documents exact collection boundary. Architecture
  remains the existing task identity contract; no new requirement selection.
- AC-5: Review and land the scoped change. Diagnostic runtime evidence must
  not become native provider or release admission.

## Cooperative Review
Implementation: astra_debug; execution: lunar_tests; final reviewer and merge:
root. No new public interfaces or scaffold helpers. Existing collection API is
the regression entry. No workflow/skill/command behavior changes.

## Phase
scoped-fix-reviewed

## Evidence
Red: four executed, three failed, exit 1. Green: four executed, zero failed,
exit 0. Explicit Rust diagnostic opt-in only; deployed pure-Simple crashed
before execution. Native qualification remains OPEN with bootstrap/runtime
owner; source-matched runner is the unblock. Root independently reviewed the
guard placement and fixtures. Astra exact-diff review: no P0/P1 findings.
