# Bench Baseline — 2026-04-18

## Host info

```
Linux dl 6.8.0-107-generic #107-Ubuntu SMP PREEMPT_DYNAMIC Fri Mar 13 19:51:50 UTC 2026 x86_64
CPU:    AMD Ryzen Threadripper 1950X 16-Core Processor
MHz:    ~2031 (measured at run time; boost varies)
Cores:  32
RAM:    125 GiB
Runner: src/compiler_rust/target/bootstrap/simple (interpreter mode)
Clock:  extern fn rt_time_now_nanos() → clock_gettime(CLOCK_MONOTONIC) via
        src/runtime/platform/unix_common.h (wired 2026-04-18, FR-BENCH-CLOCK-001)
```

## Bench: spostgre WAL append (`bench/spostgre_wal_append.spl`)

In-process shim only. No real NVFS/NVMe/FUA involved.
Measures: CRC32 framing, record serialisation, sequential-scan cost.

| Scenario | iters | min (ns) | p50 (ns) | p99 (ns) | p99.9 (ns) | max (ns) | total (ns) |
|---|---|---|---|---|---|---|---|
| wal_append_256B_x1000 | 1000 | 20 759 | 23 134 | 34 796 | 69 242 | 69 242 | 23 560 355 |
| wal_commit_group_10rec_x100 | 100 | 8 687 | 9 498 | 18 175 | 18 175 | 18 175 | 999 786 |
| wal_recover_tail_1000rec_x10 | 10 | 5 522 513 | 5 614 347 | 6 027 069 | 6 027 069 | 6 027 069 | 56 777 668 |

### WAL CSV (raw)
```
label,iters,p50_ns,p99_ns,p99_9_ns,min_ns,max_ns,total_ns,kops_per_s
wal_append_256B_x1000,1000,23134,34796,69242,20759,69242,23560355,0
wal_commit_group_10rec_x100,100,9498,18175,18175,8687,18175,999786,0
wal_recover_tail_1000rec_x10,10,5614347,6027069,6027069,5522513,6027069,56777668,0
```

Note: `kops_per_s` column is 0 because the inline `_wresult` shim used `(iters*1000)/total_ns`
which underflows for ns-scale totals. True kops/s: wal_append ≈ 42, wal_commit ≈ 100.
The `bench.lib.timing` library uses the corrected formula `(iters*1_000_000)/total_ns`.

### WAL interpretation

- `wal_append` p50 ≈ 23 µs — dominated by interpreter loop overhead, not framing cost.
  On native-compiled code, expect < 1 µs (pointer-bump + CRC32).
- `wal_recover_tail` p50 ≈ 5.6 ms per 1000-record scan — O(n) sequential scan in
  interpreter; native expect < 50 µs.
- Real NVMe FUA latency (50–200 µs) will dominate on real hardware; shim is 3–4 orders
  of magnitude cheaper.

---

## Bench: NVFS arena throughput (`bench/nvfs_arena_throughput.spl`)

**BLOCKER — interpreter speed.** A1 scenario (1000 outer × 1000 inner appends × 8 byte
pushes = ~8M push ops) did not complete within 120s interpreter budget.
No numbers recorded. Reduction to ITER=10 outer recommended for next run.

---

## Bench: fs_driver MountTable (`bench/fs_driver_mount_table.spl`)

**BLOCKER — compiler error.** `examples/nvfs/src/driver/fs_driver_impl.spl` uses
`namespace` as a struct field name, which collides with the Simple reserved keyword
`namespace` (treated as `mod` keyword). The import chain
`std.fs_driver.mount_table → fs_driver_impl.spl` fails at parse time.

Error site: `fs_driver_impl.spl:158` — `namespace: Namespace` field declaration.
Root cause: pre-existing field-naming conflict; tracked separately.
No numbers recorded.

---

## Bench: run_all (`bench/run_all.spl`)

**BLOCKER — same namespace collision** as fs_driver bench above.
`run_all.spl` imports `std.fs_driver.mount_table` for the mount-table mini-bench.
No numbers recorded.

---

## Changes made to wire real clock (FR-BENCH-CLOCK-001)

`bench/lib/timing.spl` updated:
- Replaced `var g_bench_tick: i64` loop-counter proxy with
  `extern fn rt_time_now_nanos() -> i64` call.
- `bench_now_ns()` now returns real monotonic nanoseconds.
- `bench_print` output labels updated from `total_ticks`/`ops/ktick` to
  `total_ns`/`kops/s`.
- `bench_csv_header` updated from `*_ticks`/`ops_per_ktick` to `*_ns`/`kops_per_s`.
- Throughput formula corrected: `(iters * 1_000_000) / total_ns` → kilo-ops/s.

Note: the WAL and NVFS arena benches have inline copies of the timing helpers
(duplicated for standalone-run capability). Their `_wresult`/`_result` throughput
formula still uses the old `(iters*1000)/total` and will show 0 for ns-scale totals.
These will be fixed when the benches are next updated.

---

## Pending: FR-BENCH-BASELINE-001

Baseline recorded for WAL bench. NVFS arena and MountTable benches blocked
as noted above. Re-run after:
1. Fix `namespace` field name in `fs_driver_impl.spl` (unblocks fs_driver + run_all).
2. Reduce NVFS arena A1 outer iterations to 10 (unblocks arena bench in interpreter).
3. Or: native-compile mode once FR-COMPILER-001/002 resolved (all benches will run
   in < 1s at native speed).
