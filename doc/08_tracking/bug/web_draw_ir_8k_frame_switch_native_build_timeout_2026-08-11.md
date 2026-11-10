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

## Addendum 2026-11-11 — P3 boot15 lane triage (worktree simple-p3-boot15-20261111, base f7640d20a458)

**Verdict: BLOCKED — kept OPEN (PARTIAL FIX; NATIVE 8K EVIDENCE OPEN).**

- The named JIT blocker is resolved: the sibling record
  `vulkan_engine2d_native_jit_missing_rt_struct_receiver_valid_2026-08-12.md` is
  CLOSED (Resolved 2026-08-15 — panic gone, both integration specs PASS on the fixed
  binary), and `rt_struct_receiver_valid` is defined in-tree
  (`src/runtime/runtime_native.c:8541`, declared `src/runtime/runtime.h:436`). The
  "make `rt_struct_receiver_valid` available to the self-hosted JIT runtime closure"
  acceptance item is satisfied by that resolution; do not re-chase it.
- The executable gate `scripts/check/check-web-draw-ir-8k-frame-switch.shs` now runs
  the bench with `--mode=jit` under a 180 s budget (`SIMPLE_TIMEOUT_SECONDS`
  overridable) instead of requiring a full native-build — a strictly lower barrier
  than the 2026-08-11/08-12 attempts. The bench fixture exists unchanged at
  `test/05_perf/graphics_2d/bench_web_draw_ir_8k_frame_switch.spl`.
- What is still missing is everything in "Acceptance": the reusable native artifact
  (or at minimum one JIT-mode receipt row proving `status=pass`,
  `revision_render_count=1`, `revision_reuse_count=200`, checksum, p95 <= 12.5 ms,
  RSS, fallback=false, readback mode). The prior lane's three-cycle cap is exhausted,
  and on this Windows host BOTH `native-build` and JIT-heavy closure compilation are
  in the known-live native-build hang class — this lane records BLOCKED and does not
  retry a hung build. No 8K/80 claim is made.

**Grant (non-Windows host, x86_64-unknown-linux-gnu, self-hosted binary preferred):**
`SIMPLE_BIN=<binary> sh scripts/check/check-web-draw-ir-8k-frame-switch.shs`
(raise `SIMPLE_TIMEOUT_SECONDS` as needed; require the run to stay in JIT/native mode
— no interpreter fallback — before admitting a row), then the native-artifact leg:
`bin/simple native-build --source src --source test/05_perf/graphics_2d --entry test/05_perf/graphics_2d/bench_web_draw_ir_8k_frame_switch.spl --entry-closure --opt-level=aggressive --strip --output build/render_perf/bench_web_draw_ir_8k_frame_switch`
followed by the artifact's own seed + 200-retained-calls run and the
`pixels`-copy profile question (identity/receipt vs 132.7 MB per-hit copy).
