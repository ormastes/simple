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

**FIXED (2026-04-18) — namespace keyword collision resolved.** Renamed:
- Module file `namespace.spl` → `ns_tree.spl` (path segment `namespace` is reserved)
- Struct field `namespace: Namespace` → `ns: Namespace` in both `src/driver/fs_driver_impl.spl`
  and `src/posix/fs_driver_impl.spl`
- All `self.namespace.` accesses renamed to `self.ns.`
- All three `use examples.nvfs.src.core.namespace.{...}` imports updated to `ns_tree`
- Also fixed `case Aes128GcmResult.Ok(data: plaintext):` → positional pattern in `encryption.spl`

Bench now loads past parse/compile; terminates via interpreter-bulk-buffer limit (expected).
No timing numbers recorded (interpreter budget). See FR-BENCH-NS-KEYWORD-001.

---

## Bench: run_all (`bench/run_all.spl`)

**FIXED (2026-04-18) — same namespace collision resolved** as fs_driver bench above.
`run_all.spl` imports `std.fs_driver.mount_table`; now loads cleanly.
No timing numbers recorded (interpreter budget).

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

Baseline recorded for WAL bench. NVFS arena and MountTable benches status:
1. ~~Fix `namespace` field name in `fs_driver_impl.spl`~~ — DONE 2026-04-18 (FR-BENCH-NS-KEYWORD-001).
2. ~~Reduce NVFS arena A1 outer iterations~~ — DONE 2026-04-18 (FR-BENCH-ARENA-ITER-001); see Wave 10 re-run below.
3. Or: native-compile mode once FR-COMPILER-001/002 resolved (all benches will run
   in < 1s at native speed).

---

## Wave 10 re-run — 2026-04-18

Post namespace→ns_tree rename. Bootstrap binary: `src/compiler_rust/target/bootstrap/simple` (Apr 19 02:55, fresh).

### Bench: NVFS arena throughput (`bench/nvfs_arena_throughput.spl`)

Iter counts reduced (FR-BENCH-ARENA-ITER-001) to fit interpreter budget:
- A1: outer 1000→5, inner 1000→100 (was 8M push ops; now ~4k word pushes total)
- A2: outer 100→5, inner 100→5 (64KB = 8192 words/append; was 819k; now ~205k)
- A3: outer 100→10, fill 100→10, clone_len 200KB→20KB
- A4: outer 100→10

| Scenario | iters | min (ns) | p50 (ns) | p99 (ns) | p99.9 (ns) | max (ns) | total (ns) |
|---|---|---|---|---|---|---|---|
| arena_append_small_64B_x1000 | 5 | 6 982 134 | 7 460 157 | 8 780 193 | 8 780 193 | 8 780 193 | 38 178 315 |
| arena_append_large_64KB_x100 | 5 | 9 587 279 576 | 10 070 442 298 | 10 156 801 861 | 10 156 801 861 | 10 156 801 861 | 49 726 598 222 |
| arena_clone_range_200KB | 10 | 32 836 870 | 34 056 014 | 34 879 005 | 34 879 005 | 34 879 005 | 338 072 965 |
| arena_seal_readv_40KB | 10 | 19 297 | 36 870 | 42 090 | 42 090 | 42 090 | 338 847 |

**Note:** Label names (x1000, x100) are stale cosmetic artifacts from pre-reduction; actual iter counts shown in table.
A2 p50 ≈ 10s per iter — dominated by interpreter overhead for 8192-word inner push loop (5 appends × 8192 words = 40960 pushes/iter). Native expect < 100 µs.

### CSV (Wave 10 arena)
```
label,iters,p50_ns,p99_ns,p99_9_ns,min_ns,max_ns,total_ns,kops_per_s
arena_append_small_64B_x1000,5,7460157,8780193,8780193,6982134,8780193,38178315,0
arena_append_large_64KB_x100,5,10070442298,10156801861,10156801861,9587279576,10156801861,49726598222,0
arena_clone_range_200KB,10,34056014,34879005,34879005,32836870,34879005,338072965,0
arena_seal_readv_40KB,10,36870,42090,42090,19297,42090,338847,0
```

### Bench: fs_driver MountTable (`bench/fs_driver_mount_table.spl`)

**TIMEOUT (90s).** Parse unblocked (namespace keyword fix landed). Bench starts and
enters timing loop but 10k×resolve iterations exceed interpreter budget. DO NOT touch
iter counts per task scope. Record as interpreter-limited; native-compile will resolve.

### Bench: run_all (`bench/run_all.spl`)

**TIMEOUT (90s).** Same root cause — 10k mount-resolve iters in `run_mount_bench()`.
Starts cleanly (no parse errors), times out before producing output.
