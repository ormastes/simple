# DrawIR Sparse Dynamic 8K Attempt — 2026-08-12

Status: **FAIL / 8K80 UNPROVEN**

The canonical `7680x4320` CPU DrawIR damage benchmark was strengthened from a
full-width band to a sparse `256x128` dynamic rectangle with exact off-damage
commands and traversal receipts. Seed cost and final full readback remain
outside the timed frame loop.

Command:

```sh
SIMPLE_TIMEOUT_SECONDS=300 SIMPLE_LIB=src /usr/bin/time \
  -f 'draw_ir_damage_8k_outer_max_rss_kib=%M' \
  bin/simple run test/05_perf/graphics_2d/draw_ir_damage_8k_bench.spl
```

Observed result on the available bootstrap/interpreter route:

- wall-clock watchdog: 300 seconds, before frame receipts;
- maximum RSS: 6,620,988 KiB;
- p50/p95/checksum/readback: unavailable because initialization did not finish;
- 80 fps gate: fail (`12.5 ms` p95 was not reached or measured);
- fallback/device proof: unavailable.

This row is not production-native evidence. It demonstrates that the currently
available boxed/interpreted 8K seed/allocation route is itself a blocker and
must not be used to claim dynamic DrawIR, WebRenderer, GUI, WM, or GPU 8K80.
The benchmark source now emits selected backend, synthetic frame revision,
readback source/pixel count, considered/culled command counts, checksum, full
frame mismatches, and receipt validity when a capable deployed binary completes
it. RSS remains an outer-harness receipt.

The strengthened source compiled and entered execution on this run, but did not
complete, so none of its new per-frame receipts are promoted as measured
evidence. The off-damage rectangles are visually neutral; exact selector
membership is therefore proved by considered/culled count invariants when a
future run completes, while pixel parity proves retained-frame contents.

## 2026-08-13 self-hosted launcher revalidation

The available non-seed binary reports `Simple v1.0.0-beta` and documents source
file execution as `simple <file.spl>`. Its unsupported `run` token was first
observed to exit successfully with no output, so it was not treated as a
benchmark invocation. The documented direct form was then run once with a
90-second watchdog and outer RSS receipt:

```sh
SIMPLE_TIMEOUT_SECONDS=90 SIMPLE_LIB=src /usr/bin/time \
  -f 'draw_ir_damage_8k_outer_max_rss_kib=%M' \
  timeout 90 release/x86_64-unknown-linux-gnu/simple \
  test/05_perf/graphics_2d/draw_ir_damage_8k_bench.spl
```

It failed immediately with `missing command`, exit status `248`, and
`draw_ir_damage_8k_outer_max_rss_kib=7680`. No renderer initialization,
allocation, frame timing, DrawIR receipt, or checksum occurred. This is a
self-hosted launcher compatibility/admission blocker distinct from the earlier
boxed-interpreter timeout; it is not a DrawIR performance result and does not
alter the 8K/80 status.

A correctly quoted independent `-c 'print(123)'` probe returned the same
`missing command` response. This confirms that the binary's execution
dispatcher is nonfunctional beyond direct source-file argument parsing; it is
not a benchmark-file-specific failure.

## 2026-08-13 bootstrap executor diagnostic

The bootstrap interpreter can execute the canonical sparse retained executor
benchmark, but remains unsuitable as production-native evidence. The completed
20-frame diagnostic reported a 7680×4320 CPU target, one 256×128 (32,768
pixel) dynamic rectangle per frame, and exact full-buffer parity (zero
mismatches; checksum `141975213147783168`). It considered two commands and
culled 512 off-damage commands per frame. Timed executor-only p50/p95 were
`4,945,464 ns` / `7,263,659 ns`; final CPU readback was outside timing.

This meets the isolated 12.5 ms executor budget but does **not** overturn the
status above: the route prints the bootstrap-seed warning and excludes Web
layout, retained Web/GUI/WM publication, source/resource work, present, and
scanout. A deployed self-hosted binary must reproduce this row before it can
be promoted to a Simple 8K/80 result.

## 2026-08-14 restart12 cached-entry-closure attempt

Status remains **FAIL / 8K80 UNPROVEN**. The unadmitted candidate artifact still
exits 248 with `missing command` for both direct `-c` and source-file execution.
The production-wrapper alternative was then attempted: build the benchmark as
a cached native artifact with `native-build --entry-closure` and execute that
artifact directly.

Three bounded command variants all returned exit 0 in roughly 1.4 seconds with
no stdout/stderr and no artifact. Variant 2 created the output directory; variant 3
explicitly selected LLVM and verbose mode. Neither changed the result. Current
source contains missing-artifact fail-closed guards, so stale or miscompiled
dispatch is a hypothesis, not a proved root cause. The concrete blocker is recorded in
`doc/08_tracking/bug/self_hosted_cli_native_build_silent_no_artifact_2026-08-14.md`.

Because execution never reached the benchmark, p50/p95, checksum, numeric
readback, selected backend, fallback value, binary/source hashes, and frame
receipts are unavailable. The direct-source maximum RSS receipt was 7,424 KiB
and represents launcher failure only. No smaller
viewport, seed interpreter, or native-C-only result is substituted for the
required self-hosted 7680x4320 row.

The admission and cached-carrier resume workflow is
`doc/07_guide/ui/rendering/cached_render_entry_closure.md`; its canonical plan
is `doc/03_plan/ui/perf/render_perf_replan_parallel_teams_2026-08-07.md`.
