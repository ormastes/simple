# SPipe Folder Reverse-Reference Performance

Date: 2026-09-01  
Revision baseline: `3fdb566f18d`  
Host: Linux x86_64, Node v22, AMD Ryzen Threadripper 1950X

## Workload

`examples/05_stdlib/spipe/test/perf/folder_reverse_reference_perf_test.js`
constructs an immutable inventory with 50,000 edges and 50,001 artifacts. Of
those edges, 250 reference the requested target. Twelve cold index-and-query
samples assert the exact 250-result answer and retain p50, p95, and peak RSS.
It runs both `cli-target`, which uses the public CLI construction mode, and
`mcp-lazy`, which exercises the default index used by the MCP inventory cache.
Machine-readable retained results are in
`test/fixture/folder_reverse_reference_perf_evidence.json`.

## Evidence

| Revision / mode | p50 | p95 | Peak RSS | Materialized result rows |
|---|---:|---:|---:|---:|
| `3fdb566f18d` eager all-target index | 243.204 ms | 451.033 ms | 175,493,120 B | 50,000 |
| optimized `cli-target` | 108.856 ms | 235.651 ms | 153,067,520 B | 250 |
| optimized default `mcp-lazy` after first query | 174.952 ms | 294.186 ms | 153,341,952 B | 250 |

The retained CLI run improves p95 by 47.8%, peak RSS by 12.8%, and result-row
allocation by 99.5%. The exact default/MCP mode improves p95 by 34.8% and peak
RSS by 12.6%. MCP retains a single artifact map and lazily materializes only
targets actually requested; empty/unknown target misses are not cached, so
hostile unique target strings cannot grow the cache. Its per-inventory cache
and invalidation contract are unchanged.

## Correctness and regression gate

The focused CLI, MCP, cursor, invalidation, no-follow inventory, folder
boundary, target-specific pagination, cursor binding, and work exhaustion
suite passes 15/15 tests. The performance test fails above a
650 ms p95 or 230 MiB RSS ceiling, deliberately allowing host noise while
catching restoration of substantially worse startup/allocation behavior.

No `.spl` implementation was changed in this lane, so the Simple
OptimizerPlugin source scan is not applicable. The optimization is confined to
the packaged JavaScript SPipe reference implementation.
