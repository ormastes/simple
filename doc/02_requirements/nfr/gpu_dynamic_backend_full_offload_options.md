<!-- codex-research -->
# GPU Dynamic Backend and Full Offload — NFR Options

Select one target tier. All tiers require correctness, exact device provenance,
bounded failure, no CPU-mirror-as-GPU claims, and median/p95/RSS reporting.

## Tier 1 — Baseline integrity

Description: promote correctness and observability first. Require zero parity
mismatches, provider load/submit timeout at 5 seconds, queue bounds, no resource
growth across 100 load/session cycles, and profiles that report regressions
without a speedup gate.

Pros: earliest trustworthy integration baseline; suitable for incomplete native
host coverage.

Cons: allows GPU paths that are slower than CPU to remain production-selectable
unless policy separately rejects them.

Effort: M, approximately 8–15 evidence/profile files beyond implementation.

## Tier 2 — Balanced production promotion (recommended)

Description: Tier 1 plus warm production thresholds: provider negotiation p95
under 5 ms after OS cache warmup; cached IR-to-submit host overhead p95 under
100 microseconds for representative batches; no per-frame full provider reload;
GPU selection only when end-to-end median is at least 1.20x CPU throughput or
latency is at most 0.83x CPU; p95 regression no worse than 5%; max RSS growth
bounded and reported per workload.

Pros: prevents launch/transfer-heavy fake acceleration while remaining attainable
across Vulkan, CUDA, Metal, web, and DB workloads.

Cons: demands stable fixtures and native profiling on every promoted backend;
some workloads will correctly remain CPU-preferred.

Effort: L, approximately 15–25 evidence/profile/report files beyond implementation.

## Tier 3 — Aggressive throughput

Description: Tier 2 plus cached IR-to-submit overhead p95 under 50 microseconds,
GPU promotion only at 1.50x CPU throughput or 0.67x CPU latency, p95 regression
no worse than 2%, sustained queue-saturation tests, and explicit device-memory,
pinned-memory, transfer-bandwidth, power, and 30-minute soak evidence.

Pros: strongest evidence that GPU use materially improves production workloads.

Cons: high hardware sensitivity; likely requires batching, graph capture, pinned
memory, and workload-specific tuning before broad promotion.

Effort: XL, approximately 25–40 evidence/profile/report files beyond implementation.

