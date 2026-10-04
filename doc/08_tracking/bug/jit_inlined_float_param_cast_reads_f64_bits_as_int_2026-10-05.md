# JIT: an inlined helper's float parameter reaches a float→int cast as raw f64 bits

- **Filed:** 2026-10-05
- **Area:** `src/compiler_rust/compiler/src/codegen/mir_inline.rs`
  (`remap_param_load`) × `codegen/instr/basic_ops.rs` (`compile_cast`)
- **Status:** FIXED 2026-10-05

## Symptom

Under the JIT, the rendering_2d core/extended panel headers rendered as sparse
dotted blocks at every size. These headers are drawn with the bitmap
`Engine2D.draw_text_bg` → `text_aa_blit_buffer`. The interpreter rendered them
correctly.

For `text_aa_blit_buffer("RECT", ..., 44)`:

| mode | lit pixels |
|---|---|
| JIT | 158 |
| interpreter | 3537 |

Minimal repro:

```
fn to_i(v: f32) -> i32:
    v as i32
fn floor_i(v: f32) -> i32:
    val t = to_i(v)
    if (t as f32) > v:
        return t - 1
    t
# floor_i(-0.41666): interpreter -1, JIT -1610612736
```

## Root cause

The MIR inliner replaced the callee's `Load param` with a `Copy` of the
caller's argument vreg (`remap_param_load`). The inlined body lives in new
blocks, so that vreg became cross-block. Cross-block vregs are i64 Cranelift
Variables, and a float is stored there as promoted-f64 bits. The float→int
`Cast` then received an I64 value. On an int-typed source it does
`sextend`/`ireduce` (a path kept for mis-typed int call results), so it
converted the f64 bit pattern as an integer.

`helpers_text.spl:187` already described this as "f32 payload in the integer
return channel ... converts those raw bits as an integer".

## Fix

`remap_param_load` no longer forwards a float (`f32`/`f64`) parameter. The
inlined body reads the parameter back from its slot, which the entry `Store`
has already written at the parameter's width. Integer and other parameters
keep the forwarding shortcut, so codegen is unchanged for them.

## Evidence

- Specs in `src/compiler_rust/compiler/tests/inline_float_param_jit.rs`. Both FAIL with the fix disabled (`-161061273601` against `-103`) and PASS with it.
  - `inlined_f32_to_int_helper_floors_negative_fraction` is the repro.
  - `inlined_float_params_keep_value_across_blocks` is the generalization: f64 params, several float params, and a mixed int param.
- `text_aa_blit_buffer` under the JIT: 3537 lit pixels, the same as the interpreter. The coverage sum differs by 65/485992 because the JIT does true f32 arithmetic.
- rendering_2d_extended at 960x640: the JIT capture is byte-identical to the interpreter capture (`cmp`). At 3840x2160 the headers read correctly.
