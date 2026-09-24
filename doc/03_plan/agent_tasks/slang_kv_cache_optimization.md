<!-- codex-design -->
# Slang KV cache optimization agent tasks

Date: 2026-09-09

| Lane | Owner | Deliverable |
|---|---|---|
| Plan/design refinement | Astra | Accepted architecture, metrics, workload, and hazard contract |
| Logical telemetry and prefix plan | Primary Codex | Manager counters and longest-prefix lifecycle |
| Executor/engine integration | Primary Codex | Suffix-only prefill and mode-aware statistics |
| Matched backend profile | Primary Codex | Explicit compatible context settings |
| Qualification and report | Primary Codex | Unit/system/perf fixtures and reproducible evidence |
| Lower-model sidecars | N/A | Ownership-sensitive files require one merge owner |

Shared interfaces: `KvPageTelemetry`, `PagedExecutorObservation`, and
`EngineKvCacheStats`. System helper names: `run_matched_kv_workload` and
`assert_kv_cleanup`. Any unfinished helper must fail explicitly.

Merge owner: primary Codex session. Final reviewers: Astra, then GitHub admin
self-review. Merge requires parity, bounded-memory, cleanup, and provider gates;
latency results are reported but are not a merge threshold.
