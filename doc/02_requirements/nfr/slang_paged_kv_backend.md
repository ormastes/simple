# Slang physical paged-KV NFRs

Date: 2026-09-08.

- NFR-001 correctness: cached and cold logits meet a backend-declared numerical
  tolerance on every supported model/configuration profile.
- NFR-002 safety: ASan/UBSan, stale-handle, double-release, cancellation, and
  injected allocation/copy/decode failures show no leak or cross-request mutation.
- NFR-003 memory: measured physical KV allocation for shared prefixes is lower
  than independent-context S3 on a repeated-prefix workload; no fixed saving is
  claimed before baseline measurement.
- NFR-004 latency: record cold prefill, aligned reuse, partial-tail COW, and miss
  TTFT; promotion requires no material regression on misses.
- NFR-005 boundedness: every pool, descriptor, table, reservation, and metadata
  budget has an enforced limit and observable high-water mark.
- NFR-006 compatibility: missing or partial page ABI selects S3 without crash,
  silent downgrade claims, or mixed ownership.
- NFR-007 honesty: telemetry separately reports physical-page, shared-sequence
  precursor, opaque-snapshot, and cold paths.
