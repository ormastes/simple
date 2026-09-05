# Perf Umbrella Design — TL;DR

Machinery that makes per-domain perf work safe + measurable. Full:
[perf_opt_design.md](perf_opt_design.md).

<!-- sdn-diagram:id=perf-design-tldr
flow {
  harness[bench_harness.spl] -> report[bench_report -> 09_report+10_metrics]
  snapshot[api_surface_snapshot] -> guard[check-api-arch-guard.shs]
  opt[per-domain .spl opt] -> guard
  guard -> gate{public delta?}
  gate -> |no| land
  gate -> |yes| block
  dynsmf[dynsmf dispatch+sha] -> spec[smf_cache_reuse_spec]
}
-->

- **Benchmark:** `bench_harness.spl` (tag+mode+closure → warm/cold/throughput/RSS) → `bench_report.spl` → docs.
- **Guard (AC-8):** `api_surface_snapshot.spl` emits public-symbol SDN; `check-api-arch-guard.shs` diffs vs baseline; any public delta = RED. Quarantine 3 pre-existing broken web specs.
- **dynSMF (AC-7):** keep `simple run` content-hash; build dynSMF lane dispatch + SHA sidecar + invalidation spec.
- **No inheritance** — struct `BenchCase` + closure; tag descriptors for arch extensibility.
