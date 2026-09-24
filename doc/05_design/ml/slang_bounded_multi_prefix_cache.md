# Slang bounded serial multi-prefix cache detail design

Date: 2026-09-08. Status: implemented S2 precursor.

`slang_ggml_prefix_cache_configure(entries, bytes)` accepts 0..8 entries and a
nonnegative byte ceiling. Shrinking limits evicts LRU entries immediately. A
zero limit leaves generation on the cold-prefill path.

Each entry stores token IDs, token count, serialized sequence state, retained
bytes, and a monotonic recency stamp. Selection is longest-token-count first;
slot order breaks equal-length ties. Admission checks overflow and the total
candidate size, evicts before staging allocation, serializes into private
storage, then publishes the complete entry. Allocation/serialization failure
does not fail generation and never publishes a partial entry.

The Simple engine defaults to four entries and 2 GiB, allows callers to replace
both limits, and reports unsupported S2 gauges as `-1` for an older S1 library.
Existing hit/miss/reused/prefilled meanings are unchanged. New cumulative
counters are admissions, evictions, oversized candidate bytes, and restore failures;
resident entries/bytes are instantaneous gauges.

This design bounds snapshot staging plus retained snapshot/token bytes because
space is evicted before allocation. Allocator metadata and llama's live context
remain outside this cache budget and must be reported separately in live RSS
evidence. Full A4 requires immutable pages, leases/refcounts, per-request
contexts, and copy-on-write suffixes.
