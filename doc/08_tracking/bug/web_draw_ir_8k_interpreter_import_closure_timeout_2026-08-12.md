# Web DrawIR 8K interpreter import-closure timeout — 2026-08-12

## Status

Open. The retained Web/DrawIR 8K benchmark cannot currently produce an
interpreter evidence row because compilation/import loading consumes the entire
execution budget before `main()` runs.

## Reproduction

```sh
SIMPLE_TIMEOUT_SECONDS=240 timeout 250s \
  bin/release/x86_64-unknown-linux-gnu/simple run \
  test/05_perf/graphics_2d/bench_web_draw_ir_8k_frame_switch.spl
```

Observed result: watchdog timeout at 240 seconds with no
`WEB_DRAW_IR_8K_SWITCH` output. The earlier SPipe invocation likewise failed to
reach its examples within 180 seconds. Compiler output shows the benchmark's
`Engine2dCompositorBackend` import pulling the broad Engine2D/backend family,
including Vulkan, Metal, ROCm, OpenCL, font, environment, and process modules.

This is distinct from the existing native-build timeout: the direct interpreter
entry also cannot reach benchmark execution. It does not prove a slow retained
frame, because no frame was timed.

## Required fix and acceptance

- Provide a cached compiled benchmark artifact or narrow the production
  compositor import closure without replacing the canonical Web semantic/layout
  to `DrawIrComposition` to Engine2D path.
- The executable must reach `main()` within the tooling startup budget.
- Preserve the existing evidence fields: 7680x4320 viewport, source revision,
  backend, p50/p95, RSS, fallback, readback mode, checksum, redraw count, and
  reuse count.
- Only a measured p95 at or below 12.5 ms with exact reuse and checksum evidence
  may promote the retained Web/DrawIR lane to 8K/80 pass.
