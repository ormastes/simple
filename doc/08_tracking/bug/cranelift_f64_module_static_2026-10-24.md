# Cranelift rejects f64 module statics with literal initializers (2026-10-24)

## Symptom
Phase-3 cranelift backend rejects unit `lib.common.math.math`:
`unsupported module static 'lib_common_math_math__MATH_PI' (non-scalar type or non-const init)`

## Root cause
`cranelift_static_init_supported` (src/compiler/70.backend/backend/cranelift_codegen_adapter.spl:335)
accepts F32/F64 statics only when there is no init or the init is `Zero`.
Literal f64 inits (`MirConst` Float) fall to `case _: return false`.
`cranelift_static_init_bits_value` (same file, ~362) only maps `Int` and `Bool`, so
there is no path to encode a float.

## Real fix
Add f64/f32 bit-pattern support: in `cranelift_static_init_supported` accept the
float literal variant for F32/F64, and in `cranelift_static_init_bits_value`
return the IEEE-754 bit pattern as i64 (f32: low 32 bits). Then add a regression spec.

## Affected statics (module-level `val`/`var` of f64/f32 with literal init)
- Confirmed rejecting: `pub val MATH_PI/MATH_E/MATH_TAU/MATH_INF` in src/lib/common/math/math.spl:81-84.
- Same class elsewhere (will be rejected if reachable): src/compiler/80.driver/cache/metadata/cache_limits.spl (4),
  src/compiler/35.semantics/lint/coupling.spl (3), plus ~60 in src/lib and src/app
  (grep `^(pub )?(val|var) [A-Za-z_0-9]+: f(64|32) =`).

## Workaround status: NOT applied
The `fn MATH_PI()` rewrite would touch ~140 occurrences across ~28 files
(re-exported by src/lib/common/math/__init__.spl, src/lib/common/math.spl, src/lib/math.spl;
used by engine camera/mesh/particle/debug_draw, editor viewport3d, game2d transform,
drawing/vector, skia shaders, office sheets, specs). That exceeds the 30-site
limit, so no edit was made. Tag to use if applied: `@workaround bug=cranelift_f64_module_static_2026-10-24`.

## Fix
`cranelift_static_init_supported`/`cranelift_static_init_bits_value` now accept Float/FloatLexeme inits for F32/F64 (IEEE-754 bits; F32 low 32 bits). Loads were already typed (cranelift_load with F64/F32), no int conversion. Spec: test/01_unit/compiler/backend/cranelift_module_static_contract_spec.spl (unexecuted).
