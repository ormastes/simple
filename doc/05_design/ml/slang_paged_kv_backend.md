<!-- codex-design -->
# Slang physical paged-KV detail design

Date: 2026-09-08. Status: Astra-refined implementation contract.

Use fixed `B`-token pages. `KvPageRecord` stores identity, generation, state
(`free`, `writable`, `sealed`), occupied rows, physical bytes, checksum, and two
reference counts. `KvRequestTable` stores ordered page IDs, absolute token cursor,
private-tail ID, execution namespace, and lifecycle state. `KvPrefixRecord`
stores exact tokens, ordered sealed pages, boundary metadata, and LRU epoch.

Required provider calls are execution-namespace query, pool create/destroy, page
reserve/release/seal, occupied-tail copy, transactional table begin/push/commit/
abort, decode/prefill with explicit token indices and positions, boundary-logit
materialization, and physical-byte queries. Resolve the full group atomically
only after the complete S3 independent-request group is ready.

Forking an aligned prefix increments request references. Forking a partial sealed
tail reserves a distinct page and copies only occupied rows. Execution may mutate
only transaction-exclusive staging pages. Commit publishes table, cursor, and
new request-owned logits together; failed validation or execution aborts staging,
preserves the old table/cursor, and invalidates sampling until a successful
logits-producing commit.

For fixed page size `B`, entry `i` starts at `table_base + i*B`, independent of
occupancy. Its writable interval is `[base + valid_rows, base + valid_rows +
writable_capacity)`, with overflow rejected. Multi-page cold prefill stages and
fills several exclusive pages in one transaction; committed interior pages are
full and sealed, while only the last may retain private writable capacity.

Cache admission seals complete pages and the occupied prefix tail, then creates a
record reference. Eviction removes only record references. Limit shrink first
computes whether referenced resident pages fit; if not, it returns busy without
changing limits or records.

Exact-token comparison follows hash lookup. Execution namespace includes model
weights, tokenizer, adapter, KV dtype/layout, attention/position configuration,
tensor sharding, and provider ABI. Boundary logits are recomputed or restored only
through a provider contract covered by numerical parity tests.
