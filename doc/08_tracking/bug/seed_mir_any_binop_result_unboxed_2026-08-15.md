# Seed MIR lane: bit-op on any-typed value returns UNBOXED result, corrupting nested expressions

- **Date:** 2026-08-15
- **Status:** OPEN
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

## Wanted

Route non-Add binops with ANY-typed operands through unbox → op → rebox (or
`rt_any_*` helpers), mirroring the `rt_any_add` special case, so `any` values
obey value semantics in the MIR lane. Interpreter (`bin/simple test`) and AOT
lanes are unaffected.
