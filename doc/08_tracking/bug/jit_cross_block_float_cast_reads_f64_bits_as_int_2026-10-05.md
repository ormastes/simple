# JIT: float values reaching a float→int cast as raw f64 bits

- **Filed:** 2026-10-05
- **Area:** `src/compiler_rust/compiler/src/codegen/instr/body.rs`
  (`sync_vars_to_vregs`) × `codegen/instr/basic_ops.rs` (`compile_cast`)
- **Status:** FIXED 2026-10-05
- **Follows:** `jit_inlined_float_param_cast_reads_f64_bits_as_int_2026-10-05.md`,
  which fixed one trigger and named this latent class.

## Symptom

| shape | JIT result | correct |
|---|---|---|
| `half(-7.0) as i32` with `half` inlined | 0 | -3 |
| `clamp_pos(-2.75) as i64` (call to a float-returning fn) | -4590856870150799360 | 2 |

## Root cause

A float can reach `compile_cast` as an I64 Cranelift value in two ways, and
both carry the BITS of the promoted f64:

1. **Cross-block vreg.** These are i64 Variables, and
   `coerce_to_i64_typed` stores a float as `bitcast(fpromote(x))`. The value
   `use_var` returned was handed to consumers unchanged. An inlined callee's
   return travels this way, through a `Copy` into the call's dest vreg.
2. **Float-returning call.** The uniform i64 return slot holds the bits (see
   the `Return` lowering in `body.rs`).

The float→int arm of `compile_cast` converted any int-typed source as an
integer (`ireduce`/`sextend`). The float→float arm already decoded I64 as
f64 bits.

## Fix

- `sync_vars_to_vregs` decodes float-typed (`vreg_types` F32/F64)
  cross-block vregs back to native floats: `bitcast.f64`, plus `fdemote` for
  F32. Consumers now see the same native value they see inside the defining
  block.
- `compile_cast` float→int decodes an I64 source as f64 bits only when it is a
  float-typed `Call` result. Other int sources (unknown provenance) keep the
  integer path that the `floor(x + 0.5)` mis-typing note relies on.
- Diagnostic: `SIMPLE_DUMP_CLIF=<fn>` prints a function's Cranelift IR. It is
  the codegen twin of `SIMPLE_DUMP_MIR`, and it is how both shapes were
  located.

## Evidence

`src/compiler_rust/compiler/tests/cross_block_float_cast_jit.rs` (5 tests):

| case | without fix | with fix |
|---|---|---|
| repro: inlined return | 0 | pass |
| repro: float-fn call | bits | pass |
| generalization: if-expression merge | — | pass |
| generalization: loop-carried f64 | — | pass |
| generalization: match arms | — | pass |

Note: `main` returns the i32 exit-code slot (`build_mir_signature`), so a
JIT test that returns a negative value from `main` reads it zero-extended.
These tests keep `main`'s result non-negative.
