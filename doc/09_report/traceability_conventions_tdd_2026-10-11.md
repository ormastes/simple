# Convention kernel TDD evidence — 2026-10-11

STATUS: WARN for full feature/production qualification. Scoped native component
checks and Astra source/oracle review PASS with P0=0/P1=0. Preserve all20REQ/40AC
and WP0–WP7 from `simple_traceability_sdn_slop_final_2026-10-03.md`. No whole
acceptance criterion or requirement is marked complete by these fixture results.

## Implemented behavior

`std.common.traceability.conventions_v1` resolves unit, integration, component and
manual structural associations from supplied validated graph and policy facts.
It preserves source/container/case identities and test roles, every corroborating
rule origin, explicit exclusions and positive/negative membership dependencies.
Missing or conflicting candidates produce deterministic diagnostics; bounded
resource or incomplete/policy-mismatched input refuses with no partial Ok.

Manual associations require supplied suite/output/rule/generator bindings with a
matching captured policy-input path/digest. Bindings are queried before candidate
cardinality: an unbound mirror remains a negative lookup/diagnostic and does not
make one bound output ambiguous. Two bound outputs or conflicting bindings refuse
selection. These references are data, not authenticated provenance or extraction
from the actual manifest bytes. The trusted extractor/policy owner remains open.

## Actual stages

| Stage | Construction | Native SSpec result | Meaning |
|---|---|---|---|
| Earlier missing public module | exit1 | zero examples executed | Construction RED, not assertion RED |
| Initial resolver | exit0 |6 examples,0 failures | Supplied graph/unit/manual component controls |
| Astra causal controls before repairs | exit0 |8 examples,2 failures | Actual false manual ambiguity and uncharged group work |
| Grouped cycle2 repairs and acceptance expansion | exit0 |26 examples,0 failures | Repaired controls plus roles/identity/exclusion/budget/diagnostic checks |

The earlier construction failure is preserved in
`/home/yoon/dev/simple-traceability-cli-release-sync-20261011/build/native_probe/traceability-conventions-construction-red-20261011`.
Current immutable execution stages are under
`build/native_probe/traceability-conventions-20261011-{cycle1,review-red,cycle2}`.
Each stage retains its spec, construction log and native execution log; cycle2
freezes six production modules, the executable spec and its then-current design.
The review RED inherits unchanged cycle1 production hashes and its own frozen
spec. No old stage is relabeled as final-head runtime admission.

User authorization permits the immutable Rust seed for native construction only.
Only produced native Simple artifacts execute these specs, with stub fallback
disabled (`SIMPLE_NO_STUB_FALLBACK=1`). The seed generation and build commands remain in each construct script.
Seed SHA256: `57a5476f9c6d6ede32d188420af699dc45e39c59f82700f05902f3d1c3d624b9`.
The native SSpec runner exits0 even for the actual8/2 RED; matcher example/failure
counts in the log determine the result. Exit status alone is never used as PASS.

## Review and limits

Astra reviewed design, fixtures, source, causal controls, eight frozen cycle2
hashes and log counts. Fixture ordinary definition IDs were corrected to their
case IDs, byte counts derive from hashed text, and fixture setup independently
asserts graph validity. Both reviewed P1 defects were reproduced and repaired.

Work covers index records, all node/group traversals, rule and exclusion checks,
candidate expansion, binding queries and output emission. The minimal unit
fixture refuses at27 logical units and passes at28. Count, hard-limit, policy and
result text, mapped-path field, graph and binding preflight remain bounded.
Permuted ambiguous unit fixtures validate full diagnostic/lookup ordering only;
claim ordering and generator/exclusion permutations are not independently covered.

Remaining: graph/fact extraction and actual byte semantics, complete authenticated
policy contracts, source selection and CLI integration, explicit operation
priority/stale applicability, incremental/full equality and cache invalidation,
obligation/evidence qualification, execution identity and receipts, Slop viewer
integration,80% branch coverage measurement, selected timing/RSS NFRs, admitted
SPipe manuals and broad core/MCP/LSP verification. Canonical Stage2 construction
is still blocked by its10GB disk guard; protected admission is absent.

The earlier SDN changes landed through PR2960; remaining capture/graph/declaration
contracts are in draft PR2963. This new kernel is isolated on private
`work/traceability-conventions-20261011`; those published branches remain intact.
Host JSON/hash observations are local diagnostics, not Simple-produced or broker
authenticated receipts. No release tag or protected ref is changed.
