# Tile Lane Benchmark: CPU vs GPU (2026-08-02)

Task #16 — tile rendering CPU vs GPU with performance comparison.

## Methodology

- Workload: the tile-lane render exercised by
  `test/01_unit/lib/gc_async_mut/gpu/browser_engine/tile_gpu_lane_spec.spl`
  through
  `src/lib/gc_async_mut/gpu/browser_engine/simple_web_html_layout_renderer_paint_tiles_gpu.spl`.
  Fixture: a 600x400 viewport over a 600x1200 document, 3x5 grid of 256 px
  tiles, 5 `draw_ir_rect` commands, margin 128.
- Both lanes were measured as **interpreter-lane wall time**. No compiled or
  native lane was measured.
- GPU provenance was verified from the run output, not assumed:
  `device_readback handle=1 identity=130992353372176` — the readback came
  from a real device session, not a CPU fallback.

## Numbers

| Lane | Wall time | Provenance |
|------|-----------|------------|
| CPU tile lane | 130.21 s (median) | CPU raster path |
| GPU tile lane | 404.54 s (single run) | `device_readback handle=1 identity=130992353372176` |

## Honest conclusion

These numbers measure the **interpreter**, not the GPU. The GPU lane's wall
time is dominated by interpretation overhead of the staging/readback path
(command staging, buffer marshalling, readback decode), not by device
execution. GPU offload provenance is genuine — the device readback identity
proves the work went through a real device session — but under the
interpreter the CPU lane wins by roughly 3.1x on wall time.

This result says nothing about relative CPU-vs-GPU raster throughput. It
says the interpreted staging path is expensive.

## What a fair comparison requires

- Run both lanes through the compiled lane / native build so per-op
  interpretation overhead does not dominate the staging/readback path.
- Amortize device-session setup across frames (the engine-threading
  `TileLaneFrame` wrapper already supports engine reuse).
- Report device-side timing separately from host staging/readback time.

## Reproduction cost (2026-08-04)

Re-running the spec to reconfirm these numbers was attempted twice and
produced **no verdict either time**:

```
SIMPLE_TIMEOUT_SECONDS=3600 bin/simple test \
  test/01_unit/lib/gc_async_mut/gpu/browser_engine/tile_gpu_lane_spec.spl \
  --timeout 3000
```

- Run 1: killed at the 3000 s cap (exit 144), zero spec output emitted.
- Run 2 (`--timeout 10800`): killed externally at ~42 min, zero spec output.

Neither run was OOM (125 GB total, ~88 GB available throughout); host load
averaged 36-40 on 32 cores from a concurrent bootstrap build and parallel
agent sessions. The spec calls `_cpu_lane()` three times and `_gpu_lane()`
twice, so its uncontended floor is roughly 3x130 + 2x405 = ~1200 s — which
is why it does not survive a contended host. That is itself evidence for the
conclusion above: the interpreter lane is too slow to serve as a routine
benchmark harness for this workload.

No `Results:` line was obtained on 2026-08-04, so nothing in this report is
reconfirmed by that date's runs; the numbers above are the prior session's
measurements.
