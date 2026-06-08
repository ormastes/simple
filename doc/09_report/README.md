# Reports

Implementation reports, completion logs, and session transcripts from development work.

## Directories

| Directory | Purpose | Files |
|-----------|---------|-------|
| 2025/ | 2025 completion and implementation reports | 320 |
| 2026/ | 2026 reports | 5 |
| session/ | Raw session logs from development sessions | 31 |
| misc/ | Miscellaneous reports and analyses | 792 |

## Current Root Reports

| Report | Status | Notes |
|--------|--------|-------|
| [cross_language_perf_2026-06-08_docker_contract.md](cross_language_perf_2026-06-08_docker_contract.md) | Pass | Current contract-passing Docker-isolated cross-language profile from `scripts/check/check-cross-language-perf.shs`; pins Go `GOMAXPROCS` to `CPU_WORKERS`, includes OS-thread, cooperative-green, multicore-green runtime-pool, C pthread, and Go goroutine rows, and proves Go plus Simple multicore green beat C pthreads in the 1000-task stress gate. |
| [cross_language_perf_parallel_smoke.md](cross_language_perf_parallel_smoke.md) | Historical | Earlier contract-passing cross-language profile smoke; retained for chronology but superseded by the Docker contract report because it predates the `GOMAXPROCS=CPU_WORKERS` fairness gate. |
| [cross_language_perf_parallel_large_2026-06-07.md](cross_language_perf_parallel_large_2026-06-07.md) | Historical | Earlier large-profile evidence gated by `test/05_perf/stress/multicore_green_large_profile_gate_spec.spl`; covers large multicore-green fanout against Go goroutines and C pthread rows with `pool_used`, `parallelism`, and `queue_model=work_stealing` evidence, but is superseded for current contract evidence by the Docker report. |
| [cross_language_perf_2026-06-07_smoke.md](cross_language_perf_2026-06-07_smoke.md) | Historical | Dated pre-work-stealing-contract smoke; retained for chronology but superseded by the parallel smoke and large-profile reports for current profile-contract checks because it lacks fail-closed `queue_model=work_stealing` evidence. |
| [cross_language_perf_2026-06-06.md](cross_language_perf_2026-06-06.md) | Historical | Older pre-cooperative/multicore split report from `scripts/check/check-cross-language-perf.shs`; retained as dated evidence but superseded by the parallel smoke and large-profile reports for current gated multicore-green checks. |
| [gui_perf_benchmark_2026-06-06.md](gui_perf_benchmark_2026-06-06.md) | Generated | GUI/backend profile report from `tools/gui_perf_bench/run_all_benchmarks.shs`. |
| [qemu_gtk_wm_capture_evidence_2026-06-01.md](qemu_gtk_wm_capture_evidence_2026-06-01.md) | Pass | QEMU GTK WM capture evidence. Auto QMP launch passed with a socket, and live QMP screendump capture passed with zero sample/scene mismatches. |

## Related

- [Tracking](../08_tracking/) — bug, test, and todo databases
- [Metrics](../10_metrics/) — dashboards and coverage
- [Plans](../03_plan/) — planning docs that precede reports
