<!-- codex-design -->
# Slang physical paged-KV detail design

Date: 2026-09-08. Status: Astra-refined implementation contract.

Use fixed `B`-token pages. `KvPageRecord` stores identity, generation, state
(`free`, `writable`, `sealed`), occupied rows, physical bytes, checksum, and two
reference counts. `KvRequestTable` stores ordered page IDs, absolute token cursor,
private-tail ID, execution namespace, and lifecycle state. `KvPrefixRecord`
stores exact tokens, ordered sealed pages, boundary metadata, and LRU epoch.

Required provider calls are pool create/destroy, page reserve/release, occupied
tail copy, decode/prefill with explicit page table and positions, boundary-logit
materialization, and capability/stat queries. Resolve the full group atomically.

Forking an aligned prefix increments request references. Forking a partial sealed
tail reserves a page, copies only occupied rows, and publishes it as the request's
private writable tail. A failed copy changes no table. A failed decode publishes
nothing and frees unpublished pages; a provider that may partially mutate a
published private tail must make the request terminal.

Cache admission seals complete pages and the occupied prefix tail, then creates a
record reference. Eviction removes only record references. Limit shrink first
computes whether referenced resident pages fit; if not, it returns busy without
changing limits or records.

Exact-token comparison follows hash lookup. Execution namespace includes model
weights, tokenizer, adapter, KV dtype/layout, attention/position configuration,
tensor sharding, and provider ABI. Boundary logits are recomputed or restored only
through a provider contract covered by numerical parity tests.
