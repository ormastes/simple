# Baremetal image performance probe exits without a verdict

Status: OPEN (2026-08-12)

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
