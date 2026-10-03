# Explicit-contract generic indices

Authored REQ-005 unit inventory, not executed runtime evidence.
Eleven production-API cases cover real interned Symbols, nested optional values, empty/absent lookup, custom equality overwrite,
colliding text, enum/tuple identity, removal and reinsertion, repeated growth,
collision-heavy growth, signed hash extremes, and set deduplication/removal.

Use `std.gc_async_mut.pure.indexed_collections.{HashMap, HashSet}`; these names
are not re-exported into the general pure namespace. Existing text-only maps
remain unchanged. Both constructors require deterministic hash/equality
callbacks: equality must be an equivalence relation and equal keys must have
equal hashes. Keys and callbacks must remain stable while stored.

Expected amortized operations are O(1) with well-distributed hashes and
constant-time callbacks; worst-case lookup/removal/insertion is O(n), growth
is O(n), and storage O(n + retained bucket capacity). Capacity does not shrink.
No iteration ordering or cross-engine parity is promised by this slice.

Run using an admitted self-hosted test runtime when available. No seed fallback,
runtime PASS, measured latency, or complete REQ-005 acceptance is claimed.

The Symbol case calls the existing `Symbol.from` runtime interner rather than
constructing numeric IDs. Its runtime dependency remains unvalidated here.
The optional-value case matches the outer Some explicitly, rejecting flattening
of Some(nil) into absence even if expected-value construction would also flatten.
