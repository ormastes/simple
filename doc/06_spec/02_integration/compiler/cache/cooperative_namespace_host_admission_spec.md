# G4 cooperative namespace host admission

**Source:** `test/02_integration/compiler/cache/cooperative_namespace_host_admission_spec.spl`

**Status:** executable component/integration contract. Physical provider
qualification is `MissingEvidence` until a descriptor-bound host capability is
available.

## Scenarios

1. **Prerequisite ordering** — one inventory flag is removed at a time. The
   first missing enum is checked for root gate, writer receipt, writer
   revalidation, selected-head read, immutable sync, journal admission, head
   replacement, head-directory sync, restart reissue, namespace union, and
   qualified evidence. All-present is checked as `Ready`.
2. **Selected-head codec limits** — zero, negative, maximum, and
   maximum-plus-one journal byte counts; wrong magic; noncanonical integer
   spelling; and over-bound input are rejected.
3. **Closed admission** — pure preflight returns typed invalid-head,
   invalid-writer, or `ImmutableSyncUnavailable` refusal without constructing
   opaque host handles. Physical admission remains `MissingEvidence` until the
   host issuer provides the combined capability.
4. **Revalidation** — invalid heads are `InvalidHead`, whole-head changes are
   `StaleHead`, writer-incarnation changes are `StaleWriter`, and unchanged
   identity is `Current`.
5. **Durability/recovery** — legal prefixes are rejected before replacement;
   replacement start, confirmation, or directory evidence is indeterminate
   until the complete ordered commit is present. Complete ordered evidence is
   `Committed`.
6. **Physical provider evidence** — the missing host row is recorded as
   `MissingEvidence`; no fabricated descriptor or live-host claim is made.

## Review notes

Sol reviews interface names, enum branch coverage, canonical codec boundaries,
and exact manifest ownership. Astra reviews semantic ownership, fail-closed
authority, real assertions, and the physical-evidence boundary. The test is
not a substitute for host-level sync/restart/reader/GC evidence.
