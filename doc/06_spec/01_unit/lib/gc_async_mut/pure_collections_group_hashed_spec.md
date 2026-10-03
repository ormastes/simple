# Explicit hashed grouping

Authored manual for `pure_collections_group_hashed_spec.spl`; execution pending.
This is a bounded REQ-004 library slice, not complete planner acceptance.

The production API receives deterministic key, hash, and equality callbacks.
Equality must be an equivalence relation, and equal keys must have equal hashes.
Callbacks must not mutate keys or input during grouping. Groups retain their
first key representative and first-encounter order; members retain input order.

Nine cases cover empty input/no callbacks, identical keys, distinct keys,
mixed membership, forced collisions, negative/minimum signed hashes, 512 distinct
keys, 512 members across 16 keys, and 32 forced-collision distinct keys.
The last case expects 496 equality calls; no universal linear-time claim is made.
Callback counts do not measure allocations, bucket traversal, or elapsed time.

Run the spec once an admitted self-hosted Simple test runtime is available.
No seed execution, runtime PASS, measured scaling, or engine parity is claimed.
