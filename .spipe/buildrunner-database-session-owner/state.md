# BuildRunner database receiver

## Task Type
bug

## Refined Goal
Preserve the native database session receiver so settlement and finalization
remain real calls through the frozen producer.

## Acceptance Criteria
- Claim and reproduce native manager failure without bypassing any method.
- Use the narrow explicit receiver annotation; retain the inference bug OPEN.
- Execute an imported native red/typed-green probe with observable state change.
- Exercise error-before-settle and success-after-settle in SSpec.
- Rebuild the current manager with pinned inputs and actual cache evidence;
  attempt production Hello only if a valid manager is emitted.
- Update bug record, authored manual, feature/layer wiki and native prerequisites.
  Track canonical bug-writer unavailability without overwriting its database.
- Review exact diff and land the useful scoped fix, keeping unresolved runtime
  qualification distinct from source integration.

## Cooperative Review
Astra implementation/review; Luna bounded execution; root independent review
and merge. Probe owner exposes only settle/finish; no placeholder pass helpers.

## Phase
scoped-fix-reviewed

## Evidence and remaining ownership
Imported untyped native probe failed MIR; typed variant built and executed42
with exit0. One hosted diagnostic SSpec passed the error/success state sequence.
Corrected manager MIR/AOP307/307 passed; backend accessor failure prevented a
manager image, so actual production Hello remains unexecuted. Compiler/backend
lane owns that unblock; Darwin strict provider remains a separate prerequisite.
Canonical bug writer unavailable: preserve existing database, use documented
hand-written tracking fallback and ordinary source comment. Astra exact-diff
review and root independent review: no P0/P1 findings.
