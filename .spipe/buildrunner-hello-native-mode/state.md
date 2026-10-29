# BuildRunner native Hello output intent

## Task Type
bug

## Refined Goal
Request only the native Hello artifact declared by the fixture and prevent
reuse of the former implicit-mode cache identity.

## Acceptance Criteria
- Claim the output-intent bug; observe the exact mode/cache regression red.
- Pin one-binary mode and version the cache key; preserve all ownership policy.
- Observe fixture regression green and retain direct native compiler evidence
  separately from production worker admission.
- Update the Hello guide, authored manual, BuildRunner and bootstrap wikis,
  bug record and unresolved native qualification ownership.
- Review and land the scoped change through release/1.0.0 PR.

## Cooperative Review
Astra owns the fixture; Luna runs bounded diagnostics; root independently
reviews and merges. No new public interfaces or scaffold helpers. No workflow,
skill dispatch or compiler/runtime behavior change.

## Phase
scoped-fix-reviewed

## Evidence
Seed diagnostic red: five executed, two failed, exit 1. Green: five executed,
zero failed, exit 0. Separate direct P2 compiler Hello with admitted host SDK
values compiled and executed successfully. Production fixture/strict-worker
admission remains OPEN; bootstrap/runtime owns that unblock. Authored manual
is not generated-doc evidence. Root independent review and Astra exact-diff
review: no P0/P1 findings.
