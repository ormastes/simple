# Traceability and Slop resource requirements

Selected targets from the final report, section 19. These are targets, not measurements.

| ID | Target | Verification |
|---|---|---|
| NFR-TRC-001 | Warm commit p95 ≤500 ms, p99 ≤1 s for ≤25 changed relevant files / ≤2 MiB | 30+ samples per host; exact index and bounded dependency closure |
| NFR-TRC-002 | Warm push trace p95 ≤2 s; ordinary complete push gate ≤10 s | Existing gate dispatcher, multi-ref fixtures; measure both separately |
| NFR-TRC-003 | Warm remote trace contribution ≤5 s; ordinary required lane ≤60 s | Trusted candidate evaluation, queue/checkout excluded and separately recorded |
| NFR-TRC-004 | Trace report ≤2 s for 1,000 observations | Production runner finalization and reporting; exclude test time/artifact transfer |
| NFR-TRC-005 | Loaded Slop selection visible ≤150 ms; initial neighborhood ≤200 visible nodes | Keyboard selection, asynchronous source/layout, explicit hidden counts |
| NFR-TRC-006 | Measured cold/warm/high-fan-out startup and peak RSS | Record hardware, OS, storage, admitted binary/lane, bytes/files/closure, cache hit rate, p50/p95/p99 and sample count |
| NFR-TRC-007 | Deadlines never produce clean results for incomplete work | Timeout/missing cache/read/schema sabotage; exit 2 and explicit incomplete qualification |
| NFR-TRC-008 | Metadata checking has a small dependency closure | Import audit: no UI/codegen/GPU/test-execution imports into default trace CLI |

Linux, macOS, and Windows have independent receipts. No arbitrary RSS ceiling
is invented where the report specifies measurement. Warm, cold, and fan-out
results remain separate. Current qualification: NOT MEASURED.

Report the percentile method (nearest rank: ceiling(p × sample count)) and
sample count for every distribution. The report's minimum 30 ordinary samples
is an exploratory baseline; use larger qualification samples for tail estimates
and report uncertainty rather than presenting a 30-sample p99 as a stable tail.
