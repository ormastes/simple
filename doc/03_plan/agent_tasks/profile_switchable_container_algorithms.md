# Agent task ownership: profile-switchable containers

| Lane | Owner | Scope |
|---|---|---|
| Source attribute and typed CollectionPlan | Codex | Parser, HIR, semantic guards, MIR lowering, explanation. |
| Runtime representations | Codex | Generic set/map families, transitions, observations, value/order safety. |
| `.sprof` v2 and CLI | Codex | Metric records, admission, aggregation, file workflow. |
| Cross-engine SPipe and performance | Codex | Executable/manual evidence and NFR measurements. |
| Lower-model sidecars | N/A | No sidecar assigned in this lane. |

Merge owner: Codex. Final reviewer: Codex at normal/highest capability after executable evidence exists. Shared interface names: `AdaptiveSetAttribute`, `AdaptiveSetWorkloadProfile`, `SprofCollectionLoad`, `CollectionPlan`; no silent placeholders are permitted.

## Remaining capture implementation sequence

1. Define one bounded execution-owned `collection_capture_begin`, `note_size`, `note_lookup`, `finish`, and `abort` contract. The interpreter and native runtime must share its event semantics; the app must receive a snapshot after evaluation. An app-only Simple global cannot observe the interpreter's fresh module context.
2. Instrument attributed text and generic map/set operations once per logical event. Generic set delegates to generic map; do not count both layers. Keep lookup hit detection independent of an optional map value, preserve lifetime peak across `clear`, and filter events by admitted target/site.
3. Add `simple run --collection-profile-out=PATH` with required workload and target identifiers. Serialize the bounded snapshot through the existing `.sprof` v2 writer after execution; never open files in collection operations. Make snapshot/write failures visible and clear run state on every exit path.
4. Run a first workload, change only its algorithm attribute, load the emitted profile in a second workload, and verify exact-site reuse plus path/source/workload/target rejection. Then run interpreter/native differential and NFR checks on an admitted pure-Simple runner.
