# Web/DrawIR 8K frame-switch evidence cannot reach native execution — 2026-08-11

Status: PARTIAL FIX; NATIVE 8K EVIDENCE OPEN

The persistent `Engine2dCompositorBackend` benchmark seeds one 7680x4320 Web
DrawIR frame, then times exact producer-generation/revision reuse. It requires
one render, N cache reuses, complete checksum proof, p50/p95, RSS, fallback,
and readback mode.

Interpreter attempts with 200 and 5 retained frames both exceeded 180 seconds
before emitting a row. This does not prove cached-frame latency: 8K allocation,
seed raster, full checksum, and possible value-array returns are all inside the
process. The required self-hosted native build of the same benchmark also
exceeded 180 seconds during compilation without reporting a source diagnostic:

`bin/release/x86_64-unknown-linux-gnu/simple native-build --source src --source test/05_perf/graphics_2d --entry test/05_perf/graphics_2d/bench_web_draw_ir_8k_frame_switch.spl --entry-closure --opt-level=aggressive --strip --output build/render_perf/bench_web_draw_ir_8k_frame_switch`

## 2026-08-12 gate rerun

`sh scripts/check/check-web-draw-ir-8k-frame-switch.shs` was run once with its
built-in 180-second timeout. The JIT compiler consumed approximately 5.88 GiB
RSS and emitted dependency/use warnings but no `WEB_DRAW_IR_8K_SWITCH` receipt
before timeout. In particular, the current shared worktree reported unresolved
SIMD and font execution imports while compiling the renderer closure. No cached
replay, interpreter result, or process activity is counted as performance
evidence. The 8K Web→DrawIR frame-switch lane therefore remains blocked before
frame execution, independently of its retained-frame algorithms.

The mandatory three-cycle cap is exhausted. No 8K/80 claim is permitted.

Acceptance:

- compile the entry closure once into a reusable native artifact within the
  build-performance budget;
- separately report seed time and 200 retained calls;
- prove `revision_render_count=1`, `revision_reuse_count=200`;
- prove stable complete checksum, p95 <= 12.5ms, RSS, fallback=false, and exact
  readback/presentation mode;
- profile whether returning `Engine2dDrawIrAdvResult.pixels` copies 132.7 MB per
  cache hit; if so, replace the frame-switch API with an identity/receipt or
  shared retained-surface handle rather than copying the pixel payload.

## Partial fix

`Engine2dCompositorBackend.try_reuse_draw_ir_composition_revision` now checks
the exact cached tuple/composition/resources and returns an
`Engine2dFrameSwitchReceipt` containing only scalar retained-surface identity,
checksum, provenance, and explicit zero raster/submission/readback counters.
It does not unwrap or return `revision_cache_result.pixels`.

Focused evidence passes 3/3: exact reuse, revision miss, and same-tuple content
sabotage. The 8K benchmark now times this receipt path. The native artifact and
200-frame 8K row remain unproduced because the prior three-cycle build/run cap
is exhausted.

## JIT diagnostic after receipt extraction

The bounded evidence runner
`scripts/check/check-web-draw-ir-8k-frame-switch.shs` redirects compiler
diagnostics to `build/web_draw_ir_8k_frame_switch/run.log`, requires exactly
one evidence row, and publishes only that row. Its 2026-08-11 JIT attempt
failed before seed raster: Cranelift could not resolve
`rt_struct_receiver_valid` while compiling
`Engine2dCompositorBackend.present_rect`, `report_damage`, and `main`, then
fell back to the interpreter. This is not evidence about receipt latency or
native rendering throughput.

Additional acceptance:

- make `rt_struct_receiver_valid` available to the self-hosted JIT runtime
  closure, or lower the validity check without that missing runtime symbol;
- require the runner to remain in JIT/native mode (no interpreter fallback)
  before admitting an 8K timing row.
