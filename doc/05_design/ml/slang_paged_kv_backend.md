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
For the pinned CPU provider profile, every finite logit must satisfy
`abs(actual - expected) <= 1e-4 * max(1, abs(expected))`, matching the
underlying llama.cpp backend-sampler tolerance; sampled token IDs remain exact.

The activation classifier has six explicit physical states: provider
unavailable, model support unknown, model unsupported, pool inactive, owner
disconnected, and active. Execution mode additionally depends on a resident
context and is one of `unavailable`, `snapshot`, or `physical_pages`. Only the
active state with a resident context maps to `physical_pages`; this readiness
integration does not itself provide tensor kernels or parity evidence.

## Production activation wave

The first production activation is owned by
`std.gc_async_mut.slang.model_executor.paged_executor`. One serial owner holds the backend,
execution namespace, provider pool, `KvPageManager`, provider-handle mapping,
and lifecycle state. Logical `KvPageId` values never cross SFFI; only the
provider handle recorded by the manager is passed to `physical_page_*` calls.
The independently negotiated lightweight-request extension supplies
tokenizer/output storage and a generation-safe request identity without a
legacy llama context. Physical activation requires it; snapshot requests retain
their existing contexts and behavior.

Engine load attempts activation only after complete provider negotiation and a
successful model-specific pool creation. Pool rejection remains distinct from
model incompatibility: absent explicit support evidence, readiness reports
`model-support-unknown`. Generation dispatch changes to physical pages only
after the owner is installed. Every other state retains the complete snapshot
path and its diagnostic reason.

The owner tokenizes through backend request helpers and reads exact token IDs.
Cold prefill reserves all exclusive pages, stages one complete ordered table,
executes once, and commits once. Prefix lookup requires the same execution
namespace plus exact token comparison after hash lookup. Full sealed pages are
shared; an occupied tail is copied into exclusive staging. Exact repeats
recompute their final token with `physical_page_boundary_logits`. Decode either
copies the sealed occupied tail or appends a new page at an aligned boundary.
No cursor, logical table, cache record, or logits state advances before provider
commit succeeds.

Prefix admission and eviction use `KvPageManager` reference accounting. Its
identity, telemetry, storage-shape, and bounded-construction contract lives in
`core.page_contract`; `core.page_manager` remains the sole mutable lifecycle
owner.
Eviction drops cache references only; physical release waits until cache and
request references are both zero. Physical bytes, logical metadata, exact token
identities, and transient COW pages have independent bounds. Fallback is an
activation-time decision: unavailable, unsupported, or failed physical
activation leaves snapshot dispatch installed. Once a request starts through
an active physical owner, any capacity or execution failure terminates that
request; it is never replayed through snapshot mode, even before output.

Unload stops admission, aborts live transactions, closes or cancels requests,
evicts prefixes, releases unreferenced provider pages, destroys the pool, and
then closes the backend. A busy failure preserves owner state so cleanup can be
resumed safely.

Activation requires owner-path real-model parity over cold multi-page prefill,
aligned and partial-tail reuse, exact-repeat boundary logits, and several decode
steps. It also requires deterministic eviction, capacity exhaustion,
transaction-failure, cancellation, unload/reload, and stale-handle tests.
Benchmark snapshot versus physical cold, repeated-prefix, alternating-prefix,
and eviction workloads with identical model settings; record TTFT, decode
latency, throughput, peak RSS, physical bytes, copied rows, and reused/prefilled
tokens. No speedup or memory-saving claim is made before those measurements.

Parallel execution, continuous batching, GPU paged attention, quantized KV,
spill, and distributed transport remain outside this activation wave.
