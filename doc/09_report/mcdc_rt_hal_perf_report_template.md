# MC/DC and rt(hal) Performance Report

Status: `PENDING | PASS | FAIL | BLOCKED`  
Revision: `<git sha>`  
Host/kernel/CPU: `<exact identity>`  
Compiler binary + SHA-256: `<path> / <digest>`  
Fixture revision: `mcdc-rt-hal-v1`  
Evidence receipt: `<build/perf/mcdc_rt_hal/run.receipt>`

## Method and correctness

- Same source, optimization level, owner/global budgets, and 4,000,000-decision
  fixture for off/static/dynamic lanes: `yes | no`.
- Warm-up processes: `1`; retained processes: `7`; statistic: `p50`.
- Checksums identical across all MC/DC modes: `<value / FAIL>`.
- GNU time peak RSS and Heaptrack full-minus-empty allocation traces retained:
  `<paths>`.
- Fixed-buffer saturation observed with nonzero drop/overwrite accounting:
  `<evidence>`.
- rt(hal) Pure/C/Rust/C+Rust lanes used the same ordered 32-request fixture;
  deterministic results and provider status: `<evidence>`.

## Measurements

Copy `build/perf/mcdc_rt_hal/evidence.csv` rows here without rounding away the
raw integer values.

| Lane | p50 ns | delta vs off | peak RSS KiB | RSS delta | hot allocations | artifact bytes | `.text` bytes | saturation | status |
|---|---:|---:|---:|---:|---:|---:|---:|---|---|
| MC/DC off | | baseline | | baseline | | | | | |
| MC/DC static on | | | | | | | | | |
| MC/DC dynamic dormant | | | | | | | | | |
| MC/DC dynamic enabled | | | | | | | | | |
| MC/DC saturation | | | | | | | | | |
| rt(hal) Pure | | n/a | | n/a | | | | n/a | |
| rt(hal) C compare | | n/a | | n/a | | | | n/a | |
| rt(hal) Rust compare | | n/a | | n/a | | | | n/a | |
| rt(hal) C+Rust compare | | n/a | | n/a | | | | n/a | |
| Analyzer base | | n/a | | n/a | | | | n/a | |
| Analyzer 2E | | vs base | | vs base | | | | n/a | |
| Analyzer 2C | | vs base | | vs base | | | | n/a | |

## NFR disposition

| Requirement | Pass evidence | Result |
|---|---|---|
| NFR-001 | Explicit static-off and no-MC/DC control have equal `.text`; off has zero hot allocations; inspect lowered off artifact for absent probe symbols/calls. | |
| NFR-002 | Static-on p50 and RSS deltas <=5%; full-minus-empty allocations = 0; saturation counters valid. | |
| NFR-003 | Dormant p50/RSS <=1% and zero allocation; enabled p50 <=10%, RSS <=5%, zero hot allocation. | |
| NFR-004 | 1 MiB owner/64 MiB global default receipt plus bounded 8 KiB saturation lane with explicit counters. | |
| NFR-005 | Analyzer scaling rows at doubled E and C confirm expected O(E*C); peak auxiliary RSS remains bounded. | |
| NFR-006 | rt(hal) receipt shows bounded workers/queue/timeout/output, deterministic order, and exactly-once effect evidence. | |
| NFR-007 | Completed hot-path review below, with no unresolved regression. | |
| NFR-008 | Same-fixture timing/RSS/allocation/size/saturation/correctness evidence retained together. | |
| NFR-009 | One PASS optimizer receipt per path in `optimizer_inputs.txt`; no missing or stale digest. | |

## Ordered hot-path review (NFR-007)

| Path | Complexity | allocations/copies | layout/locality | loop hoisting | dispatch | synchronization | logging | Finding/bug |
|---|---|---|---|---|---|---|---|---|
| Static probe | O(1) | | | | | | | |
| Dynamic dormant | O(1) | | | | | | | |
| Dynamic enabled | O(1) | | | | | | | |
| Recorder | O(1) | | | | | | | |
| Analyzer | expected O(E*C) | | | | | | | |
| rt(hal) coordinator | O(cases*providers) | | | | | | | |

## Optimizer receipts and blockers

List every receipt path and digest. A missing tool, unsupported foreign route,
unparseable allocation count, checksum mismatch, compiler/runtime failure, or
unresolved performance regression is `BLOCKED`/`FAIL`, never omitted. Link each
remaining measured regression to a concrete `doc/08_tracking/bug/` entry.
