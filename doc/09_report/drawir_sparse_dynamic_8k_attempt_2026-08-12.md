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
