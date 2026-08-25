# MC/DC RT/HAL perf harness uses rejected foreign callback route

Status: OPEN — performance evidence is not admissible.

## Evidence

`test/05_perf/mcdc_rt_hal/rt_hal_fixture.spl` sends the C, Rust, and C+Rust
lanes through `rt_hal_execute_tagged`. That compatibility API deliberately
returns `RTHAL-W-PARALLEL-UNSUPPORTED` before invoking foreign callbacks, so the
runner cannot retain a valid foreign row and stops before completing the
matrix. Its `/usr/bin/time` and Heaptrack measurements also cover only the
parent process; they do not prove whole-tree peak memory or allocations in the
static comparator children.

## Required fix

Build and pin the existing `test/fixtures/rt_hal_external` C/Rust static
providers once through their typed `EnvAccessPlan`. Benchmark
`rt_hal_execute_registered_exact` with one fixed request/receipt corpus and
identical warmup/iteration counts for Pure, C, Rust, and C+Rust. Include Pure
receipt generation in every timed lane. Retain whole-process-tree peak memory
from a fresh cgroup-v2 scope; label Heaptrack as controller/Pure-only evidence
and retain separate provider allocation evidence or a typed unavailable row.
Each lane must retain PASS/BLOCKED evidence independently rather than aborting
the later lanes.

## Resume gate

Do not claim RT/HAL timing, RSS, or allocation acceptance from
`run_perf_evidence.shs` until the foreign rows use the exact registered process
route and their process-tree accounting is retained.
