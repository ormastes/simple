# DrawIR tiled 8K software evidence exceeds watchdog — 2026-08-11

Status: OPEN

The production tiled DrawIR opaque-barrier benchmark cannot complete an 8K
optimized-plus-unculled oracle comparison inside the 180-second watchdog.

Reproducer:

`SIMPLE_TIMEOUT_SECONDS=180 bin/release/x86_64-unknown-linux-gnu/simple run test/05_perf/graphics_2d/bench_draw_ir_tiled_occlusion_8k.spl`

Viewport is 7680x4320 with 510 exact/ragged 256px tiles and two full-viewport
opaque commands. The optimized lane should replay 510 tile commands and omit
510; the oracle replays 1020. Both include production submission, complete host
readback, and full-buffer checksum. Five-frame, three-frame, and finally
one-frame configurations all exceeded 180 seconds without producing a result.

This disproves readiness for an 8K/80 dynamic software claim but does not
isolate optimized raster time from the uncullled oracle and checksum. The next
evidence harness should run optimized and oracle modes as separate processes,
persist their checksums/receipts, and join the rows afterward. It must retain
the same scene and binary revision. A native self-hosted runner profile should
then separate tile command-array construction, raster, full readback, and
checksum costs.

Acceptance:

- optimized and oracle modes each emit one bounded row independently;
- complete checksums match;
- optimized row reports 510 rendered and 510 occluded operations;
- row includes p50/p95, RSS, fallback, readback mode, and revision;
- any 8K/80 pass requires p95 <= 12.5ms without cached-frame substitution.
