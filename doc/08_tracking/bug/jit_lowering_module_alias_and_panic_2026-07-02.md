# JIT HIR lowering: module-alias references and `panic` intrinsic unsupported

Date: 2026-07-02
Status: OPEN (P2)
Status re-verified 2026-08-17 by source inspection (triage shard 02).
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

## Re-verified 2026-08-17 (worker s3_rust_other) — SPLIT: panic FIXED, module alias LIVE

- `panic` intrinsic: **fixed**. `compiler/src/hir/lower/expr/calls.rs:545` —
  `"panic" => Ok(Some(self.lower_builtin_call("rt_panic", args, TypeId::NIL, ctx)?))`,
  with the bare-`panic()` default-message path at `calls.rs:415-425`.
- Module alias (`use m as g`): **still LIVE**. The only alias resolution in
  lowering is for *selective*-import aliases (`hir/lower/lowerer.rs:800-803`,
  consumed at `hir/lower/expr/mod.rs:295`); `grep module_alias` over
  `hir/lower/` returns zero hits. `g.Canvas` still reaches
  `LowerError::UnknownType` (`hir/lower/error.rs:22`) and `g.run(...)`
  `UnknownVariable` (`expr/mod.rs:282`/`:380`), and under `lenient_types` that
  becomes a silent unresolved global — so the interpreter fallback persists.
This doc should be re-scoped to the module-alias half only.
