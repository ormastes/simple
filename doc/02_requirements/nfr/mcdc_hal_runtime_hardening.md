# MC/DC and HAL Runtime Hardening NFRs

- NFR-001: Static-off controlled fixtures shall have identical emitted hot-path code and a zero-byte coverage-related text/data delta.
- NFR-002: Static-on median slowdown shall be <=2%, p95 slowdown <=5%, and peak RSS increase <=2% against the identical static-off fixture.
- NFR-003: Dynamic-disarmed median and p95 slowdown shall be <=0.5%, peak RSS increase <=0.5%, with no mapped coverage pack and no coverage event/log allocation.
- NFR-004: Dynamic-armed median slowdown shall be <=10%, p95 slowdown <=15%, and peak RSS increase <=5%.
- NFR-005: Mission-critical coverage/provider/environment storage shall be fixed before entry and statically bounded where target limits are known; event/log capacity shall be <=4 MiB by default and configurable downward.
- NFR-006: Any post-initialization allocation, evidence loss, unreported overflow, or unbounded log growth in a mission-critical-or-higher entry closure is an immediate failure regardless of aggregate performance.
- NFR-007: Every enabled provider pair shall produce identical normalized results and interaction traces; comparison order and final commit shall be deterministic across repeated and parallel runs.
- NFR-008: Normal, alpha, and beta coverage promotion shall report exactly
  100% eligible MC/DC with zero unexplained exclusions; every exclusion shall
  pass governance and freshness validation. Static-off and explicitly
  diagnostic reporting do not invoke this promotion gate.
- NFR-009: Benchmarks shall retain binary/compiler identity, warmup and sample counts, median, p95, peak RSS, allocation count/bytes, artifact section sizes, event throughput, log bytes, overflow state, and raw receipts.
- NFR-010: The feature shall use one cross-platform app/test interface; all platform differences shall remain behind HAL/provider/environment executors.
