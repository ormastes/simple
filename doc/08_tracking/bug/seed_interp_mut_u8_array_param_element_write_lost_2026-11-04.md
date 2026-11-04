# Seed interpreter: element writes into a `mut pixels: [u8]` parameter never reach the caller

- **Filed:** 2026-11-04 (vkfont3 lane)
- **Status:** FIXED in source by `bafc15f38a7` (2026-10-31 17:33, "fix(seed-interp):
  &mut params write through to the caller; [u8] mut params propagate"), already on
  `release/1.0.0`. The repro above was taken on seed `release100-7a0e6fe516f`, built
  ~3 h BEFORE that commit; the deployed seed simply predates the fix. Regression
  coverage added 2026-11-04 (u8param lane). Seed redeploy is the bootstrap lane's.
- **Platform:** aarch64-apple-darwin, seed `release100-7a0e6fe516f-20261031`
- **Blocks:** acceptance item 7 of
  `macos_vulkan_2d_vector_font_empty_batch_native_fault_2026-07-26.md`
  (`simple test` runs specs on the interpreter).

## Repro

```simple
fn fill(mut meta: [i64], mut pixels: [u8]):
    var i: i64 = 0
    while i < pixels.len():
        pixels[i] = 200u8
        i = i + 1
    meta[0] = 7

fn main():
    var m: [i64] = [0; 4]
    var p: [u8] = [0u8; 5]
    fill(m, p)
    print "m0={m[0]} p0={p[0]}"
main()
```

| mode | output |
|---|---|
| `simple run` (JIT, default) | `m0=7 p0=200` |
| `SIMPLE_EXECUTION_MODE=interpreter simple run` | `m0=7 p0=0` |

The `[i64]` out-param writes back; the `[u8]` one does not (same for a
single indexed store, and for a cross-module callee).

## Impact

`sfnt_render_glyph_into(..., mut meta: [i64], mut pixels: [u8])`
(`src/lib/common/encoding/sfnt_glyf.spl:799`) counts its coverage into
`meta[9]` (64 for '2' at 18 px) but the caller in
`FontRenderer` (`font_renderer.spl:1888`) sees an all-zero `direct_pixels`.
Every atlas cell becomes `0x00FFFFFF` (alpha 0), so under `simple test` every
TrueType glyph is fully transparent on every backend; CPU oracle and GPU then
agree on an all-blank frame.

## Fix direction

Interpreter argument passing for `[u8]` arrays (likely the packed byte-array
value representation) must alias the caller's array like `[i64]` does, on the
plain Simple-function call path in `src/compiler_rust/compiler/src/interpreter_call/`.
Do not rewrite `sfnt_render_glyph_into` around it.

## 2026-11-04 resolution (u8param lane)

Root cause (in the old seed): `var p: [u8] = ...` is packed to `Value::ByteArray`
by `coerce_to_declared_type`; the Bug #19 park/write-back
(`interpreter_call/core/function_exec.rs`, `park_written_back_arguments` /
`write_back_mutable_arguments`) matched only `Value::Array | Dict | Tuple | Object`,
so a packed byte buffer was never written back. An untyped `var p = [0u8; 5]`
stays a boxed `Value::Array` and always worked (measured). `bafc15f38a7` added the
`Value::ByteArray(_)` arms.

Evidence (seed built from `origin/release/1.0.0` @ worktree base, `cargo build --release`):

| check | old seed 7a0e6fe516f | fresh seed |
|---|---|---|
| repro, interpreter | `m0=7 p0=0` | `m0=7 p0=200` |
| repro, JIT | `m0=7 p0=200` | `m0=7 p0=200` |
| `test/01_unit/compiler/interpreter/mut_array_param_element_write_spec.spl` (interp) | 4/8 (all `[u8]` cases fail) | 8/8 |
| `cargo test --release --test interpreter_mut_u8_array_param_write_back` | — | 2/2 |

The new spec covers `[u8]`, `[i32]`, `[f64]`, `[bool]`, `[i64]`, call depth 2, a
write through an index expression, and the mixed `[i64]`+`[u8]` shape above.

Out of scope, noted: module-level `var`s passed to a `mut` array param are NOT
written back in either mode, for `[i64]` as well (`u8=0 i64=0` under both JIT and
interpreter) — consistent semantics, not this defect.

Downstream: `native_gpu_font_readback_spec.spl` Engine2D row now PASSes under
`simple test` — see `macos_vulkan_2d_vector_font_empty_batch_native_fault_2026-07-26.md`.

## 2026-11-04 note (jitalias lane)

The module-level `var` mut-param write-back gap above remains open; it is not the
same root as the JIT field-store alias fixed in
`seed_jit_class_field_array_assign_aliases_local_2026-11-04.md`.

## 2026-11-04 note (modvar lane)

The module-level `var` gap is filed and fixed separately in
`seed_interp_module_var_mut_array_param_write_back_lost_2026-11-04.md`: it was a
module-SCOPE call site only (interpreter; the no-`main` file demotes the JIT), not
a JIT defect.
