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
| [cross_language_perf_2026-06-11_thread_fix_refresh_freshbin.md](cross_language_perf_2026-06-11_thread_fix_refresh_freshbin.md) | Pass | Current contract-passing Docker-isolated cross-language profile from `scripts/check/check-cross-language-perf.shs`; preserves the broad workload inventory (artifact footprint, cold startup, warm throughput, OS-thread workers, cooperative-green, multicore-green runtime-pool, C pthread, Go goroutine, large fanout, stress fanout, hosted sliced fairness, parallel artifact footprint, and peak RSS), with optional Python/Bun/Java/Erlang rows documented when those toolchains exist; pins Go `GOMAXPROCS` to `CPU_WORKERS`; requires `used_runtime_pool()` / `pool_used=N/N` plus `counter_delta=submitted/completed,pending=0,busy=0,blocked=0` evidence for the multicore-green rows; includes `Hosted Fairness Evidence` for `multicore_green_spawn_sliced` with sliced-handle `used_runtime_pool=true` as the explicit scalar-state fairness contract while ordinary closure preemption remains future work; keeps raw `thread_yield()` inside ordinary `multicore_green_spawn` closures classified as non-preemptive gap evidence; and proves Go plus Simple multicore green beat C pthreads in the 1000-task stress gate with the refreshed green/cooperative runner. |
| [simpleos_multicore_green_evidence_2026-06-07.md](simpleos_multicore_green_evidence_2026-06-07.md) | Pass | Current SimpleOS green-carrier evidence; includes the 2026-06-14 interpreter-run refresh for cooperative, multicore scheduler, green-channel wake, and final handoff blocker specs from `/tmp/simple-pherallel-continue-jj`. The release-visible gate is the fast `simpleos_green_hardware_handoff_blocker_spec.spl` contract, while fresh AP ring/user proof remains opt-in through `SIMPLEOS_GREEN_CARRIER_QEMU_HW_HANDOFF_LIVE=1`. A 2026-06-14 live final-handoff rerun with `--timeout 240` completed without the runner timeout but failed before fresh marker proof. A later x86_64 freestanding runtime ABI fix added `rt_string_char_code_at` / `rt_for_iterable`; the current-source Cranelift build now links `build/os/simpleos_green_carrier_probe.elf`, but direct QEMU boot of that ELF timed out after 30 seconds without `[smp]` or `[green-carrier-qemu]` serial markers, and the opt-in live SSpec scheduler-lane rerun did not return usable marker output in this session. The LLVM backend is unavailable in this driver build. The current refresh blocker is tracked in `doc/08_tracking/bug/simpleos_green_final_qemu_refresh_build_blocker_2026-06-14.md`. The prior live QEMU final-handoff claim is therefore not refreshed by this report. The scheduler-only live lane must not emit `HW_HANDOFF_PASS=true`, `USER_ENTRY_PASS=true`, or `USER_SYSCALL_PASS=true`; those final markers remain exclusive to the `SIMPLEOS_GREEN_CARRIER_QEMU_HW_HANDOFF_LIVE=1` AP ring/user path. |
| [cross_language_perf_2026-06-08_docker_contract.md](cross_language_perf_2026-06-08_docker_contract.md) | Historical | Earlier Docker-isolated contract-passing cross-language profile; retained for chronology but superseded by `cross_language_perf_2026-06-11_thread_fix_refresh_freshbin.md` for current green/cooperative SSpec-runner and multicore-green evidence. |
| [cross_language_perf_parallel_smoke.md](cross_language_perf_parallel_smoke.md) | Historical | Earlier contract-passing cross-language profile smoke; retained for chronology but superseded by the Docker contract report because it predates the `GOMAXPROCS=CPU_WORKERS` fairness gate. |
| [cross_language_perf_parallel_large_2026-06-07.md](cross_language_perf_parallel_large_2026-06-07.md) | Historical | Earlier large-profile evidence covering 2000-worker stress fanout; retained for chronology, but the active large-profile gate now checks `cross_language_perf_2026-06-11_thread_fix_refresh_freshbin.md` so current contract evidence, Docker isolation metadata, pinned Go scheduler width, and OS-thread row naming stay aligned. |
| [cross_language_perf_2026-06-07_smoke.md](cross_language_perf_2026-06-07_smoke.md) | Historical | Dated pre-work-stealing-contract smoke; retained for chronology but superseded by the parallel smoke and large-profile reports for current profile-contract checks because it lacks fail-closed `queue_model=work_stealing` evidence. |
| [cross_language_perf_2026-06-06.md](cross_language_perf_2026-06-06.md) | Historical | Older pre-cooperative/multicore split report from `scripts/check/check-cross-language-perf.shs`; retained as dated evidence but superseded by the parallel smoke and large-profile reports for current gated multicore-green checks. |
| [gui_perf_benchmark_2026-06-06.md](gui_perf_benchmark_2026-06-06.md) | Generated | GUI/backend profile report from `tools/gui_perf_bench/run_all_benchmarks.shs`. |
| [qemu_gtk_wm_capture_evidence_2026-06-01.md](qemu_gtk_wm_capture_evidence_2026-06-01.md) | Pass | QEMU GTK WM capture evidence. Auto QMP launch passed with a socket, and live QMP screendump capture passed with zero sample/scene mismatches. |

## Related

- [Tracking](../08_tracking/) — bug, test, and todo databases
- [Metrics](../10_metrics/) — dashboards and coverage
- [Plans](../03_plan/) — planning docs that precede reports
