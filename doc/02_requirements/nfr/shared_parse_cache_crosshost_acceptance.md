# Shared parse cache acceptance bounds

- NFR-001: Run all production host processes through SOSIX's owned capacity
  boundary. Proof reservations: Linux at most 2 GiB; Windows at most 7 GiB when
  admitted; manager 4 GiB; preserve the coordinator's 8 GiB host reserve.
  Verify with actual capacity, process-tree and peak-memory receipts.
- NFR-002: Bound each fixture with the admitted worker timeout. Retain elapsed
  time and peak memory for cold publication and cold-private shared hydration.
  Do not invent a performance improvement from parser-call elimination alone;
  no latency target has been accepted for this correctness gate.
- NFR-003: Preserve existing shared/private caches and failed-run artifacts.
  Negative tests operate on new diagnostic roots holding copied genuine cells.
- NFR-004: Retain immutable hashes of source authority, parser identity,
  compiler/runtime image, output image, cell, payload, command and logs with
  actual host/process receipts. Missing evidence blocks deployment.
- NFR-005: Check each unchanged acceptance criterion once; at most three
  fix/verify cycles. A resource or compiler failure is reported without
  unbounded retry or silently substituting the Rust seed.
