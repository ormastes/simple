# GUI 8K dynamic-render evidence is blocked by native renderer artifact build time

- **Id:** gui_8k_native_renderer_artifact_build_timeout_2026-08-13
- **Status:** OPEN
- **Severity:** P1 — blocks a valid pure-Simple 8K/80 dynamic-render claim on an
  available GPU host
- **Found:** 2026-08-13
- **Component:** self-hosted native-build startup / GUI performance harness

## Symptom

The canonical GUI benchmark now builds the smallest supported native renderer
artifact once, then invokes that artifact directly for CPU-SIMD and software
rows.  This avoids measuring the raw-source interpreter startup in each frame
sample.  On the available Linux host with an NVIDIA RTX A6000, the artifact
build does not complete within the explicit 30-second evidence bound:

```text
gui_perf_benchmark_artifact_build_status=failed
gui_perf_benchmark_artifact_build_us=30006343
```

The runner marks the CPU rows `native_artifact_build_failed`; it does not emit a
frame timing, checksum, or a misleading 8K/80 pass.  The deployed `bin/simple`
also identifies itself as a Rust bootstrap seed, so it cannot supply the
required pure-Simple evidence in its place.

On 2026-08-13 the bundled `bin/simple_native --version` was also tried as a
possible direct native launcher. It immediately terminated with
`timeout: the monitored command dumped core`, before emitting provenance or a
version. It is therefore unavailable for benchmark evidence and must not be
substituted for the required self-hosted artifact.

## Related bounded observations

- GTK at 7680x4320 completed its one-frame draw-only row in **81.460 ms**
  (about 12.3 fps), not the 12.5 ms 80-fps target.
- The CUDA raw-source row exceeded its 30-second per-backend bound and was
  recorded as `wall_timeout_30s`.
- The previous raw-source CPU-SIMD route exceeded a 180-second bound before it
  produced a frame receipt.  That is a tooling/startup measurement, not renderer
  throughput evidence.

These observations do not establish a CPU or GPU throughput regression: no
current, non-seed native renderer artifact completed to provide a valid frame
row.

## Reproduction

From a clean benchmark output directory, use the bounded harness:

```bash
BENCH_TIMEOUT_SECS=30 bash tools/gui_perf_bench/run_all_benchmarks.shs \
  --width 7680 --height 4320 --frames 1 --dpi 300
```

The artifact entry is
`src/app/wm_compare/backend_measurement_software_export.spl`; the harness builds
it with only `src/app` and `src/lib` source roots and `--entry-closure`.

## Required fix

Make a non-seed self-hosted native-build path available for the supported
renderer entry within the bounded build budget, or provide a cached, provenance-
identified artifact produced by that path.  The resulting benchmark evidence
must include viewport, revision, backend, p50/p95, RSS, fallback state, and
checksum/readback proof before 8K/80 can be claimed.

## Mitigation landed

- `d9860ac755c` builds and reuses the direct renderer artifact instead of
  repeatedly launching the raw source wrapper.
- `c4546cd6c9f` and `7891e92170a` bound per-backend execution and artifact
  build time, leaving unavailable rows explicit and preventing orphaned work.

## Related

- `doc/08_tracking/bug/bootstrap_stage3_selfhost_seed_wrapper_fallback_2026-06-17.md`
- `doc/08_tracking/bug/check_costs_two_seconds_per_function_decl_2026-08-10.md`
- `doc/09_report/gui_perf_benchmark_2026-08-13.md` (generated local evidence;
  do not treat it as an 8K/80 pass)

## 2026-08-17 triage — BLOCKED, not re-measured in this lane

Read and left OPEN with its blocker intact. Deliberately **not** re-measured
here rather than reported on weakly: closing it requires either a working
self-hosted `native-build` or a QEMU/board evidence run, and both are outside
this lane's budget and permissions (one test process at a time, no main-compiler
build).

One relevant fact measured today that bears directly on the native-artifact half
of these blockers: `bin/simple native-build` currently fails outright on a
twelve-line struct probe with `error: semantic: undefined field 'kind': cannot
access field on value of type 'nil'` (gate:
`scripts/check/check-aot-smoke.shs` → `FAIL — AOT lane broken`). So the AOT lane
is broken ahead of any performance question — a native-renderer or DrawIR
artifact build cannot succeed while that holds, and re-attempting these
benchmarks before it is fixed would only re-derive the same blocker. Detail:
`doc/08_tracking/bug/aot_llvm_void_type_struct_probe_2026-08-10.md`.
