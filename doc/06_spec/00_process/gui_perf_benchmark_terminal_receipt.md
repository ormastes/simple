# GUI Performance Benchmark Terminal Receipt

## Purpose

This process contract defines when a GUI performance profile is a complete
benchmark run. It applies to the canonical supervisor
`tools/gui_perf_bench/run_all_benchmarks.shs` and its Markdown reports under
`doc/09_report/`.

The profile may contain useful completed backend rows before a later lane
fails or is terminated. Those rows remain historical observations, but they
do not make the profile a complete Simple CPU, GPU, Web, GUI, WM, or 8K/80
result.

## Canonical Producer and Outputs

Run the supervisor from the repository root, selecting a fresh report and
build directory for the run:

```sh
BUILD_DIR=build/gui_perf_bench_<run-id> \
REPORT_PATH=doc/09_report/gui_perf_benchmark_<run-id>.md \
tools/gui_perf_bench/run_all_benchmarks.shs --width 7680 --height 4320 --frames 60 --dpi 300
```

The canonical report is the `REPORT_PATH` written by that invocation. Per-lane
stdout, stderr, and `/usr/bin/time -v` data stay in its matching `BUILD_DIR`.
Do not merge rows from separate reports into a synthetic completion result.

## Terminal Receipt Rule

Exactly one terminal receipt must appear in the report:

- A complete run ends with
  `gui_perf_benchmark_harness_status=completed` and
  `gui_perf_benchmark_harness_exit_code=0`.
- A failed or externally interrupted run ends with
  `gui_perf_benchmark_harness_status=failed`, a nonzero exit code, and a
  reason. A deadline receipt additionally identifies
  `gui_perf_benchmark_harness_receipt_owner=detached_supervisor`.
- A report header, a partial backend section, or a missing terminal receipt is
  an incomplete harness result. It cannot support a throughput, RSS, checksum,
  or 8K/80 claim for unfinished Simple lanes.

The supervisor owns the normal deadline through
`GUI_PERF_BENCH_HARNESS_TIMEOUT_SECONDS` (default 150 seconds). Its detached
supervisor writes a failed terminal receipt from a separate session when an
outer resource guard kills the benchmark process group. Consumers must retain
that failure rather than interpreting an absent backend row as unavailable or
passing.

## Result Admission

1. Confirm one completed terminal receipt before reading Simple backend timing.
2. For each claimed lane, require its backend status, dimensions, frame count,
   timing distribution, RSS, checksum/readback or pixel proof, execution mode,
   and fallback state in the same report.
3. Keep prior reports intact. For example,
   `gui_perf_benchmark_2026-08-12_cpu_8k_terminal_receipt.md` is historical
   partial evidence; its GTK and Node rows remain external references, while
   its Simple rows are not admitted measurements.
4. Feed only fresh lane-specific normalized receipts to the final
   `scripts/check/check-render-8k80-receipt.shs` and
   `scripts/check/check-render-8k80-matrix.shs` admission gates. The complete
   lane/resume matrix is
   `doc/03_plan/ui/perf/render_perf_resume_matrix_2026-08-12.md`.

## Focused Contract Check

```sh
sh test/05_perf/profile_scripts/gui_perf_bench_terminal_receipt_contract_test.shs
```

This check validates ordinary completion and an externally killed benchmark
group. It is a workflow-contract test, not an 8K performance measurement.
