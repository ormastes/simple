# Historical chain and key-retention regression slice

Traceability: REQ032 historical evidence, REQ019 exact/aggregate distinction,
and REQ030 retained evidence integrity. These are source regressions, not
runtime or performance qualification.

`setup_item2_history_chain()` returns an existing signed Reference history
fixture plus three actual retained-rollup CAS digests and the final retention
head. The target observation stays pinned while real retention owners produce
generations one, two and three. Unpinning then deletes its raw CAS object with
the generation-three rollup recorded by the real deletion/retention owners.
No test directly invents a deletion receipt or authoritative catalog.

The query must prove generation-three coverage and replay dependencies through
two and one. Missing or tampered prior bytes must never yield Aggregated.
Two-hop and cumulative byte limits must stop before opening an unavailable
third object, with semantic, retention and checkpoint heads unchanged.

`setup_item2_history_without_producer_key(fixture)` independently signs and
installs into a fresh actual repository a same-epoch checkpoint with a policy
that no longer contains the original producer key, retaining the original
accepted registry and actual metadata pages. Query may still report
checkpoint-attested evidence; this is
not verification of the absent original producer signature. Replaying the old
signed producer patch must fail current admission. Removing or replacing the
independently pinned checkpoint verification key must reject the query.
The existing single-policy installer cannot authenticate an old anchored
checkpoint under a changed policy; same-root policy rotation remains outside
this test slice and is explicitly rejected, not simulated as an import.

The existing `setup_item2_history` signature is unchanged. Its restricted case
now uses the real owned-key/AEAD store and verifies decryptability during
fixture setup. Historical query itself never loads that key. Observation
fixtures use the reviewed uppercase PASS outcome grammar.

Non-goals: epoch migration, remote authority admission, transitive evidence
hydration, aggregate policy redesign and original-signature provenance claims.
Paged historical cases are owned by the parallel Paged lane.
