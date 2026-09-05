# MIR Local Symbol Index Specification

MIR lowering retains `local_symbol_ids` and `local_symbol_values` as its
stage-safe authoritative binding store. A flat open-address table stores only
integer slots into those arrays. It never stores `LocalId` payloads or relies on
mutation of a dictionary field.

The executable fixture binds forty symbols deliberately colliding at the
initial capacity, crosses resize thresholds, checks every result, updates an
existing symbol without growing the authoritative arrays, and checks negative
and missing symbols. It removes the cache beside live authoritative arrays to
prove lookup fallback and bind-time repair without duplicate append, then
repeats that proof for an out-of-range occupied slot. It also snapshots all three binding components, overlays
an existing and a new symbol, restores them, and proves the overlay cannot leak.
Reset evidence proves symbol reuse in a later function.

Static lifecycle assertions pin the sole constructor initialization, the shared
per-function reset, and both lambda save/restore sites. These checks prevent a
future scope rollback from restoring authoritative arrays while leaving stale
index slots.

At load below 70%, binding and lookup are expected O(1) with worst-case O(L)
linear probing; geometric rebuild is O(L) and amortized across insertions. The
single flat i64 slot table adds O(L) memory. At capacity between roughly 1.43L
and 2.86L after doubling, its payload is about 11.5–22.9 bytes per live binding,
excluding the authoritative arrays and headers. During resize, old and doubled
tables briefly coexist at roughly 34.3 bytes per binding near the grow point;
a lambda overlay can likewise trigger an O(L) COW table copy. No timing, allocation, RSS,
compiler, or runtime execution was performed under the user override.
