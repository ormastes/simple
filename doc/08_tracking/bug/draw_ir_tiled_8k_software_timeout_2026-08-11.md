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

## Triage addendum (2026-11-11, lane ne7)

**Status: LIVE — remains OPEN; out of scope for a P3 traverse lane.**

Re-checked on the release/1.0.0 tip (branch work/p3-ne7-20261111):

- `test/05_perf/graphics_2d/bench_draw_ir_tiled_occlusion_8k.spl` is
  unchanged in shape since the report: still 7680x4320, 510 tiles, both
  `engine2d_draw_ir_render_tiled` and `engine2d_draw_ir_render_tiled_unculled`
  in one process with full readback + checksum (`git log --follow` shows only
  merge/lineage commits touching the file; last content-bearing change
  predates this bug).
- No split-process optimized/oracle evidence harness and no separately
  bounded per-lane rows exist anywhere in `test/05_perf/graphics_2d/`,
  `var/lib/`, or `build/` (grep for the acceptance row markers finds nothing).
- The 2026-10-27 v3 triage freeze
  (`doc/08_tracking/bug/triage_20261027/evidence_v3/lane01_accepted.md`)
  classifies this `valid / untested / keep_open` with the same remaining work
  (collect separately bounded optimized/oracle rows on identical
  scene/revision with matching checksums).

Not re-run here: an 8K software raster bench cannot produce honest evidence
in interpreter mode on the Windows lane, and the acceptance criteria
(split-process harness, native runner profile, p95 <= 12.5ms at 8K/80) are a
perf-infrastructure build, not a P3 fix. No green rerun attempted per
runaway-guard rules.
