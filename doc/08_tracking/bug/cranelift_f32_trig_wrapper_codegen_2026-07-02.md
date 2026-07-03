# Cranelift JIT: f64→f32 trig wrapper bodies fail codegen (engine3d)

Date: 2026-07-02
Status: fixed (2026-07-03) — engine3d raster path now JIT-compiles; see residual items below
Severity: P3
Found by: W6 lane agent

## Symptom

```
JIT compilation failed ... Cranelift JIT compile: Module error: codegen:
7 function body/bodies failed to compile:
[_sin, _cos, _tan, _sqrt, gpu3d_sqrt_f32, gpu3d_sin_f32, gpu3d_cos_f32]
```

The Cranelift verifier rejected the f64→f32 trig wrapper bodies in
`src/lib/nogc_sync_mut/gpu/engine3d/` (math_hooks/simd_kernels3d).
Because any failed body hard-fails the whole module compile, the ENTIRE
engine3d program fell back to the interpreter (W6d rollball run listed 28
stubbed bodies: mat4_*, vec3_*, gpu3d_*_f32, emu_*, collide_*, Quaternion.*).

Measured consequence (game.rollball, 800x600, CpuBackend3D, host under a
concurrent bootstrap): per-frame render p95 ≈ 2.9 s idle → 12–26 s under load,
versus the master-plan G4.x target of ≤ 33 ms.

## Root cause (chain of six defects, all in the seed JIT/codegen)

The verifier error (`fdemote.f32 of an i64`) was the visible tip of a chain:

1. **rt_math_* unresolvable by the JIT symbol provider** — the shims were
   missing from `RUNTIME_SYMBOL_NAMES`
   (`src/compiler_rust/common/src/runtime_symbols.rs`), so `run_file_jit`
   classified them as unresolvable externs and the hybrid transform rewrote
   every call into an `InterpCall` interpreter round-trip. `InterpCall`'s
   result-unboxing has a known f64 gap (`rt_value_raw_i64` instead of
   `rt_value_as_float` when the dest vreg is untyped), which fed a raw i64
   into `fdemote` → verifier rejection.
2. **rt_math_* missing from `RUNTIME_FUNCS`**
   (`codegen/runtime_sffi.rs`), so even a direct call would have been
   declared with the uniform `(i64,…)->i64` signature instead of the real
   `f64` C ABI.
3. **`compile_cast` float↔float branch ignored the tagged-i64 ABI**
   (`codegen/instr/basic_ops.rs`) — cross-block floats travel as promoted-f64
   bits in i64; `fpromote`/`fdemote` on them is a verifier error (hit once
   `_sin`/`_cos` became inlinable).
4. **f32 was broadly broken in the seed JIT** (pre-existing, masked because
   engine3d never JIT-ran):
   - f32 param prologue read raw low-32 f32 bits while callers pass
     promoted-f64 bits (`instr/body.rs`);
   - float-returning fns coerced the return with `fcvt_to_sint` (value
     conversion) instead of preserving bits (`instr/body.rs`);
   - `compile_store` silently replaced any f32-local store with `f32const 0.0`
     on type mismatch (`instr/memory.rs`) — `val x: f32 = 3.0` became 0.0;
   - binop/unary reinterpretation only handled `TypeId::F64`, not `F32`
     (`instr/core.rs`, `instr/basic_ops.rs`).
5. **Name-only virtual dispatch** (`mir/lower/lowering_expr_method.rs` +
   `lowering_core.rs`): a concrete class sharing a method NAME with any trait
   (e.g. `Engine3D.name()` vs trait `RenderBackend3D.name`) was lowered as a
   vtable call; `Engine3D` has no vtable, so slot-0 dispatch jumped through
   field data → SIGSEGV. Engine3D delegates ~50 same-named methods.
6. **Typed-array & file-IO marshalling bugs** exposed once the JIT actually
   ran the render loop:
   - `inline_numeric_arg` heuristic untagged any raw value that is a multiple
     of 8 (`instr/calls.rs`) — framebuffer colors 0xFF202020/0xFF00CC00 were
     stored as `value>>3`;
   - `rt_file_write_text`/`rt_file_append_text` were in the wrong marshalling
     table (`text_cstr_arg_indices` ptr-only instead of `text_arg_indices`
     (ptr,len) pairs) and had 2-param specs for a 4-param C ABI — every
     JIT `write_file` returned false.

Plus one pure-Simple fix: `_rasterize_triangle_vk` was missing `mut` on its
backend param (`src/lib/gc_async_mut/gpu/engine3d/backend_vulkan.spl`),
rejected by the stricter JIT lowering (W1006).

## Fix (files)

- `src/compiler_rust/common/src/runtime_symbols.rs` — add all 33 rt_math_* shims
- `src/compiler_rust/compiler/src/codegen/runtime_sffi.rs` — rt_math_* specs
  with real f64 ABI; fix rt_file_write_text/append_text to 4-param specs
- `src/compiler_rust/compiler/src/codegen/instr/basic_ops.rs` — tagged-i64-aware
  float↔float cast; unary-op reinterpret for F32/F64
- `src/compiler_rust/compiler/src/codegen/instr/body.rs` — f32 param prologue
  (bitcast.f64 + fdemote); bit-preserving float returns into i64 slots
- `src/compiler_rust/compiler/src/codegen/instr/memory.rs` — f32/f64 store
  conversions instead of zeroing
- `src/compiler_rust/compiler/src/codegen/instr/core.rs` — binop reinterpret_f64
  covers F32
- `src/compiler_rust/compiler/src/codegen/instr/calls.rs` — type-aware
  inline_numeric_arg (raw value for typed-words set); move write/append_text
  to (ptr,len) marshalling
- `src/compiler_rust/compiler/src/mir/lower/lowering_core.rs` +
  `lowering_expr_method.rs` — receiver-aware trait dispatch
  (`find_trait_for_method_on_receiver`)
- `src/lib/gc_async_mut/gpu/engine3d/backend_vulkan.spl` — `mut backend`
- `src/app/game.rollball/game.spl` — `SIMPLE_ROLLBALL_MODE=perf` perf-only mode

## Verification (seed rebuilt cranelift-only, profile bootstrap)

- `examples/11_advanced/game3d_smoke/main.spl`: **0** failed bodies (was 7),
  `GAME3D_SMOKE PASS` fully JIT-compiled (depth-correct occlusion, correct
  colors, evidence PPM written). Previously required whole-program
  interpreter fallback.
- 800x600 two-triangle raster probe, same scene/host (concurrent bootstrap
  load): p95 **8434 ms interpreted → 150 ms JIT (~56×)**.
- Specs under the fixed seed: `math3d_spec`, `vec3_spec`, `mat4_spec`,
  `float_unit_spec`, `float_edge_spec`, `common/math/math_spec` all PASS.
  (`engine3d_spec` fails identically on the pre-fix seed — pre-existing.)

## Residual — 2026-07-04 update: rollball now FULLY PASSES under JIT

`GAME3D_ROLLBALL PASS`, all 10 gates (SESSION/WINSTATE/LOSESTATE/DISTINCT/
MOTION/OCCLUSION/CAMERA/VULKAN/HUD + evidence PPMs), fully JIT-compiled, no
env override needed. Physics matches the interpreter to ~13 significant
digits (win final x=9.0554 JIT vs 9.0724 interp — fp reassociation only).
800x600 perf probe: p95 **12,386.8 ms interpreted → 172.5 ms JIT (~72x)** on
this loaded 7.4 GiB host (probe reports p95-of-5 only; no p50 output).
`GAME3D_SMOKE PASS` fully JIT. Specs green under the fixed seed: `math3d`,
`vec3`, `mat4`, `float_unit`, `float_edge`, `common/math/math_spec`.

Fixed in this pass (all seed-side):

- Cross-module private `_sin/_cos/_sqrt/_tan` f32-vs-f64 collision: colliding
  bare `_name` defs are emitted as `_name$dupN` and call sites resolve by
  exact arg-type match (arity-unique → extern → last-def fallback)
  (`mir/lower/lowering_core.rs`, `lowering_expr_call.rs`).
- `Array.add_dynamic`/`add_static` unresolved: duplicate `PhysicsWorld3D`
  class in the flattened unit (physics/world3d.spl pulled simple/world3d.spl
  just for `Joint3D`) mis-typed `self.bodies` as the other class's array
  field. Fixed by extracting `simple/joints3d_data.spl` (both nogc trees).
- `gpu.engine2d` no longer routed to the interpreter by
  `should_prefer_interpreter_for_source` (`driver/src/exec_core.rs`).
- Module-level typed f32/f64 globals initialized to 0.0 under codegen:
  `try_const_eval` had no float path → initializer dropped. Rollball's
  START_X/GOAL_X/VEL_CAP were all 0.0 (ball "won" at step 1)
  (`hir/lower/module_lowering/module_pass.rs`).
- Global const arrays with suffixed literals (`18842895918i64`, the shared
  5x7 font table) silently dropped → zero glyphs (HUD FAIL) or SIGSEGV via
  the trusted inline `len` deref of the zero slot; `try_const_eval` now
  accepts `Expr::TypedInteger`.
- `x ** 0.5` miscompiled: float Pow used an integer-exponent fmul loop
  (`fcvt_to_sint(0.5)` = 0 → x**0 = 1.0; broke `math_sqrt`). Now calls
  `rt_math_pow` (`codegen/instr/core.rs`).
- Raw f64-bits-in-i64 call args (cross-block floats) were VALUE-converted by
  `adapt_value_to_type`'s int→float arm — `math_sqrt(dist_sq)` computed
  sqrt(4.6e18)≈2.14e9 in the physics narrowphase (ball fell through the
  floor). Args typed F32/F64 in `vreg_types` are now bitcast back to f64
  before signature adaptation (`codegen/instr/calls.rs`).
- Statically-typed concrete receivers with their own `Type.method` are
  devirtualized (direct call) instead of vtable-dispatched — fixes
  `SoftwareBackend.init` SIGSEGV (`mir/lower/lowering_core.rs`).

Still open (separate bugs):

- 172 ms > 33 ms G4.2 target for the 800x600 probe on this loaded host;
  profile when idle.
- Duck-typed trait dispatch (trait with zero `impl Trait for ...`, e.g.
  game2d `App`/`GameBackend` driving `LoopDriver.step`) has no vtable to
  dispatch through. Live sites now emit a named runtime diagnostic + trap
  (sentinel `DUCK_DISPATCH_UNSUPPORTED_SLOT`) instead of silently jumping
  through field data; dead sites cost nothing. Breakout headless therefore
  still needs `SIMPLE_EXECUTION_MODE=interpreter` (completes 120 frames) —
  real fix tracked in jit_game2d_backend_method_dispatch_sigsegv_2026-07-02.
- `imported_fn(...) ?? default` corrupts the result under JIT (e.g.
  `env_get("X") ?? "all"` → empty; broke `SIMPLE_ROLLBALL_MODE` routing —
  perf-only mode falls through to "all"). Direct extern + `??` and local fn
  + `??` are fine; imported-wrapper + `??` is the failing shape.
- Untyped module-level float globals (`val A = -9.0`, type ANY) and
  `arr.len()` results type-inferred as the array's own type (prints "0.0")
  remain broken under JIT.
- `InterpCall` f64 result-unbox gap (dest vreg untyped → `rt_value_raw_i64`)
  still exists for any extern that remains genuinely unresolvable.
- Worktree hazard (tooling, not codegen): for a source file at the worktree
  ROOT, `resolve_use_to_path`'s parent walk reaches the MAIN checkout's
  `src/std` (worktrees live under `<repo>/.claude/worktrees/`) before trying
  the worktree's own `src/`, silently compiling the wrong tree. Files under
  `<worktree>/src/**` resolve correctly.
