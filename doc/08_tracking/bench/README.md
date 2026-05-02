# Benchmark Baselines

This directory holds committed baseline CSV snapshots for Phase 9 storage
benchmarks. Committing baselines across revisions enables regression detection
without requiring a live environment.

## Convention

Baseline filenames: `<bench_name>_baseline_<date>.csv`

Examples:
```
run_all_baseline_2026-04-17.csv
fs_driver_mount_table_baseline_2026-04-17.csv
```

## How to Capture

```bash
bin/simple run test/perf/bench/run_all.spl > doc/08_tracking/bench/run_all_baseline_$(date +%F).csv
```

## How to Compare

```bash
diff doc/08_tracking/bench/run_all_baseline_2026-04-17.csv \
     doc/08_tracking/bench/run_all_baseline_2026-04-18.csv
```

The CSV header row is: `label,iters,p50_ticks,p99_ticks,p99_9_ticks,min_ticks,max_ticks,total_ticks,ops_per_ktick`

## Disclaimer

Current baselines measure **tick counts** (loop-counter proxy), not real
nanoseconds. See `test/perf/bench/README.md` for the full disclaimer and
FR-BENCH-CLOCK-001 (real CLOCK_MONOTONIC binding).
