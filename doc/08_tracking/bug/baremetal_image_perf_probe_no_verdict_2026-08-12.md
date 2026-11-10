# Baremetal image performance probe exits without a verdict

Status: OPEN — BLOCKED (2026-11-11, P3 lane ne2): receipt counters verified green on the refreshed seed; the p50/p95 timing verdict still needs a native or SimpleOS/QEMU host

## Symptom

A focused `test/05_perf` probe comparing a full image scan with the bounded
visible scan launched the self-hosted child binary but emitted no example or
file verdict. The outer runner also returned no usable exit code.

Three bounded attempts reproduced the failure: a 512x512 fixture using
`time_now_unix_micros`, a 128x128 fixture using the same clock, and the reduced
fixture using the graphics harness' `rt_time_now_nanos` primitive. Per the
runaway guard, the probe was removed rather than retried.

## Evidence retained

`backend_baremetal_image_clip_spec.spl` proves exact output and work receipts:
an 8-pixel source clipped by the framebuffer examines exactly 4 pixels, while
mask, alpha, and clip behavior remain exact. `BaremetalBackend` exposes
`last_image_source_pixels` and `last_image_examined_pixels` for a future native
or QEMU benchmark without inference.

## Required resolution

Run the receipt-backed probe through a stable native or SimpleOS/QEMU timing
entrypoint and record p50/p95, checksum, RSS, viewport, backend, binary
revision, and fallback state. Do not use the 256x work-reduction ratio alone as
an 8K/80 performance claim.

## Fix attempt — 2026-11-05 (work/libbug-linux-imgprobe-20261105)

Root cause: the work-receipt counters `last_image_source_pixels` and
`last_image_examined_pixels` documented above as exposed by `BaremetalBackend`
were absent from `src/lib/gc_async_mut/gpu/engine2d/backend_baremetal.spl`, so
the retained receipt-backed probe
`test/01_unit/lib/gc_async_mut/gpu/engine2d/backend_baremetal_image_clip_spec.spl`
failed semantic analysis with `class BaremetalBackend has no field named
last_image_source_pixels` — the probe exited with an ERROR verdict recap and
no usable example/file verdict semantics, and the outer runner returned no
usable exit code, matching this report.

Fix: restored both counters on `BaremetalBackend` (class fields, constructor
init, and per-call accounting in `draw_image`; examined counts pixels passing
the bounds/clip intersection before mask gating). Verified with the phase1
snapshot CLI on aarch64 Linux: the clip spec now reports
`SPEC FILE VERDICT ... outcome=OK declared>=3 executed=3 passed=3 failed=0`
and exit 0.

Environment limit: this host is aarch64 Linux; the x86_64 baremetal /
SimpleOS QEMU p50/p95 benchmark required for full resolution was not run.


## Verdict addendum — 2026-11-11 (P3 lane ne2)

Verdict: **BLOCKED** (status stays OPEN) — the receipt-side defect is fixed and
re-verified; the timing-verdict half of "Required resolution" cannot run in this
lane's environment.

Verified this lane on the refreshed seed (`bin/simple.exe`, build-commit
`0791c2b7f4a7`, seed-smoke `--mode=interpreter --no-cache`, Windows x86_64 host):

- `test/01_unit/lib/gc_async_mut/gpu/engine2d/backend_baremetal_image_clip_spec.spl`
  → SPEC FILE VERDICT OK, 3/3 passed. The restored
  `last_image_source_pixels` / `last_image_examined_pixels` counters emit example
  and file verdicts with a usable exit code — extending the 2026-11-05 aarch64
  Linux evidence to x86_64 Windows.

Still missing (the actual subject of this record): p50/p95, checksum, RSS,
viewport, backend, binary revision, and fallback state from a **stable native or
SimpleOS/QEMU timing entrypoint**. This host has no `qemu-system-*` on PATH, and
this lane is forbidden cargo/rustc and entry-closure native builds, so the timing
probe cannot be produced here.

Grant to unblock: on a Linux host with the self-hosted binary, run the
receipt-backed bounded-scan vs full-scan probe through the SimpleOS x86_64 QEMU
timing entrypoint (or a `native-build` probe with `SIMPLE_KEEP_NATIVE_OBJS=1`)
and record the metrics above; until then this row remains OPEN-BLOCKED, not a
performance claim.
