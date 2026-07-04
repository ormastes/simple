# JIT HIR lowering: module-alias references and `panic` intrinsic unsupported

Date: 2026-07-02
Status: open (workarounds in place)
Severity: P2 (every affected program silently falls back to the interpreter)
Related: doc/08_tracking/bug/jit_lowering_clamp_f_engine_color_2026-07-02.md

## Symptoms (each observed on breakout, 2026-07-02)

1. **Module-alias references fail lowering** — both types and calls:
   - `use std.game2d as g` then `fn draw(ctx: g.Canvas)` → `Unknown type: g.Canvas`
   - `g.run(...)` → `Unknown variable: g while lowering main`
   - `use ...input.api as input_api` then `input_api.set_current(...)` →
     `Unknown variable: input_api while lowering LoopDriver.step`
   The interpreter resolves all of these fine.

2. **`panic` intrinsic unknown to lowering** —
   `Unknown variable: panic while lowering now` (game2d det_guard).

## Workarounds applied

- game2d examples + `loop/driver.spl` + `app/run.spl` now use direct
  `use module.{name}` imports instead of module aliases.
- det_guard uses a local `_det_panic` (print + `rt_exit(1)`).

## Expected

HIR lowering should resolve `alias.member` exactly as the interpreter does,
and `panic` should lower to the runtime abort path. Until then, any library
using module aliases quietly loses JIT for the whole program — the perf
cliff is ~100x (one breakout frame: <1 s JIT-target vs >280 s interpreted).
