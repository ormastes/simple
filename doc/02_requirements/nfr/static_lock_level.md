# Static lock-level nonfunctional requirements

- Unannotated modules return before resource scans or graph allocation.
- Maximum 4096 ranked declarations and graph nodes; at most 100000 declaration
  metadata/AST work units, depth 256, 4096 edges per node, and 200000 graph units.
  Exhaustion is E-LOCK-LEVEL-003, never a clean result.
- Metadata uses process-local typed owners, canonical flat-pool encoding and
  explicit transient promotion. No per-declaration environment mirrors.
- Native/shared frontend behavior and cache refusal must agree.
- Runtime locking gains no checker calls or tracking allocations.
- Startup/RSS/latency and repeated warm cache lifetime behavior need measurement
  with an admitted pure-Simple producer before production-readiness approval.
