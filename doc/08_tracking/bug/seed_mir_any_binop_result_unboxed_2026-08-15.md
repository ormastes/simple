# Seed MIR lane: bit-op on any-typed value returns UNBOXED result, corrupting nested expressions

- **Date:** 2026-08-15
- **Status:** RESOLVED (2026-08-15)
- **Area:** src/compiler_rust/compiler/src/mir/lower/lowering_expr_ops.rs (ANY-operand BinOp lowering) / MIR execution lane used by `bin/simple run`
- **Severity:** correctness — silent wrong integers, no diagnostic

## Symptom

Under the seed's `bin/simple run` lane, binary bit/arith ops whose operand came
from an `any`-typed array element compute the right integer but return it in
the WRONG representation, so nested expressions decode garbage.

Minimal repro (probe run 2026-08-15, seed `bin/simple run`):

```simple
fn body(mut dst: any):
    val d = dst[0]              # element of a [u32] passed as any
    print "{d}"                 # 1344853885  (0x5028D77D) — correct
    print "{d >> 24}"           # prints 10   (should be 80; 10 == 80 >> 3)
    print "{d & 0xFF}"          # prints <value:0x7d> (raw 125, undecoded)
    print "{(d >> 24) & 0xFF}"  # a ~4e-322 denormal == f64::from_bits(80)
fn main():
    var dst: [u32] = [1344853885]
    body(dst)
```

Interpretation with the runtime's tagging (`RuntimeValue::from_int` = `v << 3`,
TAG_INT = 0, TAG_FLOAT = 2, src/compiler_rust/runtime/src/value/core.rs:237):
the BinOp on ANY operands yields the correct integer 80 but **unboxed** (raw
80, not `80 << 3`). A consumer that decodes it as boxed sees `80 >> 3 = 10`;
raw 80 has tag bits `80 & 7 == 0`… while `(d>>24)&0xFF` chains produce values
whose tag bits land on TAG_FLOAT, printing as `f64::from_bits(80)` denormals.
`lowering_expr_ops.rs:292-303` emits a plain `MirInst::BinOp` for non-Add ops
on ANY operands (only `Add` is routed through `rt_any_add`), with no
box/unbox normalization; sibling comments in the same file reference the same
raw-vs-boxed family as "#66".

An explicit cast (`val d = dst[idx] as u32`) pins the value to a typed lane
and everything downstream computes correctly — that is the workaround.

## Real-world impact

This was the actual root cause of
`engine2d_native_blend_diverges_from_scalar_on_varied_patterns_2026-08-15.md`:
`_scalar_blend_row` (dst param typed `any`) mis-computed `da/dr/dg/db` on
350/640 varied bench pixels, making the pure-Simple *reference* diverge from
the (correct) native C/Rust kernels. Fixed there with the `as u32` workaround;
the underlying lowering bug remains open here.

## Resolution (2026-08-15)

Fixed in `src/compiler_rust/compiler/src/mir/lower/lowering_expr_ops.rs`
(`lower_binary_expr`): the existing mixed-ANY unbox block was extended to
cover ANY+ANY operands for the non-Add arithmetic/bit/compare ops
(Sub/Mul/Div/Mod/BitAnd/BitOr/BitXor/Shl/Shr/Lt/Gt/LtEq/GtEq) — each ANY
operand is unboxed (`UnboxInt`/`UnboxFloat`), the native `BinOp` runs on raw
values, and — the actual defect — the raw result of an arithmetic/bit op is
now **re-boxed** (`BoxInt`/`BoxFloat`), since these expressions are ANY-typed
and every consumer decodes the tag-boxed representation. Comparisons stay
raw (bool i64 0/1). ANY+ANY `Add` remains on `rt_any_add` (string concat).
No new runtime symbols needed (pure MIR insts), so `runtime_symbols.rs`
is unchanged.

Evidence (deployed seed `bin/release/x86_64-unknown-linux-gnu/simple`,
2026-08-15):
- Repro now prints `1344853885 / 80 / 125 / 80` (was `…/10/<value:0x7d>/denormal`)
  under both `bin/simple run` (JIT) and `SIMPLE_EXECUTION_MODE=interpreter`.
- `test/perf/graphics_2d/bench_span_kernels.spl` checksum `316643543` under
  both `SIMPLE_2D_SIMD=off` and `auto`.
- `test/01_unit/lib/gpu/engine2d/simd_kernels_config_matrix_spec.spl` 18/18.
- New regression spec:
  `test/01_unit/compiler/50.mir/any_binop_boxed_result_spec.spl` (7/7) covering
  `>>`, `&`, `|`, `^`, `-`, `*` and a nested chain on any-typed elements.

### Float ANY+ANY follow-up (TODO closed 2026-08-15)

The remaining TODO — ANY+ANY non-Add ops assumed integer operands
(`UnboxInt`), so a float-valued any operand computed on raw bits — was
confirmed failing and fixed the same day.

Repro (f64 array passed as `any`, elements 7.75 and 2.5): before the fix,
`bin/simple run` (JIT) printed `sub=-64`, `mul=912910859327140449`, `div=0`,
`lt=true`/`gt=false` (inverted), `chain=NaN`; interpreter was correct.

Fix: added tag-dispatch runtime helpers mirroring `rt_any_add` —
`rt_any_sub`/`rt_any_mul`/`rt_any_div`/`rt_any_mod` (boxed result; float lane
when either operand `is_float()`, else wrapping int lane) and
`rt_any_lt`/`rt_any_gt`/`rt_any_le`/`rt_any_ge` (raw i64 0/1, matching the
comparison convention) in
`src/compiler_rust/runtime/src/value/collections.rs`. MIR lowering
(`lowering_expr_ops.rs`) now routes ANY+ANY Sub/Mul/Div/Mod/Lt/Gt/LtEq/GtEq
through these calls; bit/shift ops stay on the UnboxInt path (no float lane).
Registered in `common/src/runtime_symbols.rs` (JIT symbol table) and
`compiler/src/codegen/runtime_sffi.rs` (RuntimeFuncSpec, so native/.smf
captures the result).

Evidence (rebuilt + redeployed seed, 2026-08-15):
- Float repro now prints `5.25 / 19.375 / 3.1 / false / true / 10.5` under
  both `bin/simple run` (JIT) and `SIMPLE_EXECUTION_MODE=interpreter`.
- `test/01_unit/compiler/50.mir/any_binop_boxed_result_spec.spl` extended
  with 5 float cases (sub/mul/div/compares/chain): 12/12.
- `test/01_unit/lib/gpu/engine2d/simd_kernels_config_matrix_spec.spl` 18/18.

## Wanted

Route non-Add binops with ANY-typed operands through unbox → op → rebox (or
`rt_any_*` helpers), mirroring the `rt_any_add` special case, so `any` values
obey value semantics in the MIR lane. Interpreter (`bin/simple test`) and AOT
lanes are unaffected.
