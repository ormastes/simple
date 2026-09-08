# Slang physical paged-KV requirements

Date: 2026-09-08. Status: selected Astra-refined contract.

- REQ-001: Retain S3 as a complete fallback and negotiate physical paging as a
  separate all-or-nothing backend capability group.
- REQ-002: Allocate fixed-token-capacity physical pages from a generation-tagged
  pool; never expose addresses across SFFI.
- REQ-003: Give each request an ordered block table and one private writable tail.
- REQ-004: Seal published prefix pages; appending to a shared partial tail must
  reserve, copy occupied rows, and write only the private copy.
- REQ-005: Establish equality with exact tokens and execution configuration;
  hashes are indexes, not authority.
- REQ-006: Count cache-record and request-table references independently and
  reclaim a page only at zero references.
- REQ-007: Bound physical KV bytes, descriptors, token metadata, requests, and
  transient COW reservations before allocation.
- REQ-008: Evict deterministic LRU cache records while referenced pages remain
  resident and accounted; reject unsatisfiable shrink atomically.
- REQ-009: Publish pages and advance request cursors only after successful decode;
  failure releases reservations and unpublished pages.
- REQ-010: Recompute boundary logits into private storage and prove cached versus
  cold numerical parity.
- REQ-011: Cancellation and teardown release each reference once; unload requires
  zero live request/cache owners or an explicit cache purge.
- REQ-012: Reject stale pool/page/request handles and all model, tokenizer,
  adapter, KV-layout, attention-config, or position mismatches.
- REQ-013: Do not call opaque serialized-state chunks pages.
- REQ-014: Keep one serial execution owner until parallel advancement is proven.
- REQ-015: Production physical requests allocate tokenizer/output identity and
  bounded token storage without allocating a parallel legacy llama context;
  negotiate this request mode separately and retain legacy requests unchanged.
