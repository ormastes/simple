# Profile-switchable ordered-map operation counts

**Requirement:** NFR-PSC-002. **Executable spec:** `test/05_perf/collections/profile_switchable_ordered_operation_count_spec.spl`.

**Status:** Written, not executed on an admitted source-matched pure-Simple runtime. No performance PASS is claimed.

The spec inserts sorted integer keys into a production `OrderedMap` at 128, 256, 512, and 1024 entries. Its update counter records equality and native-order comparisons made by the real insertion and removal paths; its lookup counter uses the same search path as `get` and `contains_key`. Both counters include the constant-time native key validation checks. At every size it checks contents and length, a fixed logarithmic height limit, insertion comparisons below four times that limit plus a constant, hit/miss comparisons below twice that limit plus a constant, and removal comparisons below six times that limit plus a constant. It removes and reinserts a key and requires allocated node slots to remain at the prior peak live size.

These are operation-count and node-slot bounds for the ordered representation only. The slot check is an internal storage proxy; it does not measure allocator calls or retained byte size. Linear comparisons, hash probes, copied bytes, RSS, warm latency, and behavior on every target profile have separate gates. The spec must run through a qualified source-matched pure-Simple runtime before its result is accepted. The existing general collection benchmark scripts do not substitute for this spec.
