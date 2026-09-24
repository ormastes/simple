# Slang independent request-context test plan

- REQ-001/002/005: bounded admission includes the compatibility request.
- REQ-003/004: stale, wrong-generation, closed, and prior-model handles reject.
- REQ-006/007/008: shared-prefix pins survive pressure; eviction/shrink cannot
  reclaim live bytes and failed shrink leaves the prior policy unchanged.
- REQ-009: unload returns busy with a live request and Simple does not `dlclose`.
- REQ-010: cancel/close/failure release each context and lease exactly once.
- REQ-011/012: full S3 symbols enable the capability; partial ABI uses S2 wrappers.
- REQ-013: two requests interleave deterministically but no thread-parallel claim appears.

The deterministic C fixture compares two interleaved requests against isolated
oracles and injects allocation, serialization, restore, truncation, decode, and
close failures. ASan covers slot reuse and teardown. Real llama evidence must
prove cross-context restore/output parity and per-context RSS before release.
