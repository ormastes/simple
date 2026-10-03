# Collection profile and memory bridge specification inventory

Status: **authored companion, incomplete as a generated manual, unexecuted**
(2026-10-03). Source:
`test/01_unit/app/optimize/sprof_collection_profile_spec.spl` (22 scenarios).
This inventory summarizes the whole file and details its three new memory
bridge scenarios. It is not SPipe docgen output or evidence of passing tests;
omitted implementation detail is not accepted coverage.

## Existing scenario coverage

The first 17 scenarios cover source identity without perturbing parser state;
attribute-switch identity while retaining path/code distinctions; generic
integer map/set and text-map observations; automatic attributed construction
feedback; embedded-target isolation; distinct marginal p95 samples; measured
profile roundtrip and exact-site selection; rejection of other target/workload
feedback; prepared prior admission only for automatic matching instances;
provable set metrics; merging runs with distinct samples and counters; file
persist/reload; malformed/ambiguous record rejection; nearest-rank p95;
admitted profile bridge selection; and paired hash/collision metrics through
prepared and one-off selectors.

The final two scenarios cover named P6 metric persistence and distribution
summaries, and rejection of malformed metrics or duplicate sample identities.
They do not by themselves prove all collection lowering, profile provenance,
cross-engine parity, memory estimation, or performance requirements. Existing
`in-development` tagging and linked tracking report remain applicable.

## New memory admission scenarios

The shared fixture provides proved semantic/target facts and a same-site
population bound of 100, with supplied candidate memory costs. These values
represent **proof-owner upper bounds on peak extra bytes across the full
supported population**, including simultaneous candidate storage. They are
not total RSS, average allocation, measured peak for one sample, or values
derived from profile p95 cardinality. A hot profile refines workload cost;
it cannot provide or relax a memory proof.

| Scenario | Concrete fixture | Required observable result |
|---|---|---|
| Admitted feedback cannot supply an unknown memory budget through any bridge | Admitted site profile size 100/lookups 1000; budget -1; finite linear/hash/ordered bounds | One-off, prepared-profile and prepared-metrics selectors all return Original with `memory-budget-unproven` |
| Profile selection preserves exact supplied memory bounds and rejects one byte over | Linear 32, hash 512, ordered 768 extra bytes; budget 512 then 511 | Hash fits exactly with static-only and admitted-profile automatic selection, and through all three explicit-hash bridge paths. Budget 511 rejects explicit hash with `memory-budget-exceeded`; automatic selection returns Original and exposes both indexed candidates over budget |
| Hot feedback cannot invent a candidate memory estimate or repair invalid memory facts | Explicit hash, budget 512, unknown hash cost -1 then malformed -2 | All three bridges retain unknown-cost rejection `memory-estimate-unproven`; one-off invalid-cost input returns Original with `invalid-memory-facts` |

These scenarios invoke real serialization, parsing, profile indexing and
production bridge/selector APIs. They do not synthesize selected decisions.
The bridge copies the complete supplied facts and resets only profile fields;
the tests protect memory facts against loss or accidental profile replacement.
Legitimate earlier selection fixtures now supply finite independent bounds;
unknown-facts negative fixtures have not been silently legalized.

## Evidence still required

No runtime RED/GREEN was observed for this increment. Missing fields at the
test-first revision and static source inspection are not executed RED evidence.
An admitted self-hosted runtime must execute the scenarios, retain exact
source/runtime identity and assertion results, and generate/review the complete
manual through SPipe docgen before any generated-manual acceptance claim.

The tests accept supplied memory proofs; they do not implement proof production,
validate a runtime allocator's peak usage, or demonstrate that a selected MIR
plan actually executed. Profile identity coverage here must not be expanded
into unsupported claims about every backend/key/registry/epoch combination.
REQ-009/010/011 and NFR-004/007 remain incomplete at full feature scope.
