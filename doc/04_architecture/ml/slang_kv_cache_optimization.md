<!-- codex-design -->
# Slang KV cache optimization architecture

Date: 2026-09-09

This wave extends the existing serial `paged_executor` owner; it does not add a
second cache owner. `KvPageManager` remains authoritative for logical identity,
references, admission, LRU, and copy-on-write. The backend remains authoritative
for tensor pages and execution. The engine selects the mode and projects
mode-aware observations. A separate perf fixture owns workload sequencing and
evidence publication.

For candidate tokens `C`, the executor calls `find_longest_prefix(scope, C)`.
It validates the retained token count and page rows, maps sealed full pages,
copies a partial final page to a private writable page, evaluates the required
boundary token when no suffix exists, otherwise prefills `C[prefix_len..]`, and
commits one native and logical transaction. Failure aborts staging and leaves
the published prefix unchanged.

Observations are monotonic counters attached to the owner generation. Snapshot
and physical observations use a tagged projection; unavailable fields remain
unavailable rather than borrowing counters from another mode. Cache identity
continues to include the execution namespace and exact token sequence.

The benchmark uses public prompts and fresh processes per mode/workload. It
separates model activation from resident request timing and labels logical
bytes, provider bytes, and process RSS independently.

Deferred: parallel requests, GPU paging, SSD spill, distributed reuse,
cross-tenant sharing, and default activation.
