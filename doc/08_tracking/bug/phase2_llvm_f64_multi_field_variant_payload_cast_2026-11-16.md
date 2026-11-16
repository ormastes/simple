# Phase-2 LLVM: `bitcast ptr to double` for f64 field of a multi-field enum variant

Status: FIXED in this change (backend cast emission). Found by a frozen Phase-2 build
(pin 18a1f28937c2) compiling `src/compiler/50.mir/_MirLoweringExpr/expr_dispatch.spl`.

## Symptom
`case FloatLit(value, _)` on `HirExprKind.FloatLit(value: f64, suffix: text?)`
(`src/compiler/20.hir/hir_definitions.spl:617`) emitted
`%x = call ptr @rt_tuple_get(i64 %payload, i64 0)` then `bitcast ptr %x to double`;
llc: "invalid cast opcode for cast from 'ptr' to 'double'". A single-payload f64
variant emitted the valid `bitcast i64 %p to double`.

## Root cause
`llvm_bitcast_impl` (`src/compiler/70.backend/backend/_MirToLlvm/aggregate_intrinsics.spl`)
handled ptr<->int, i1, int<->int, but its final `else` printed `bitcast <src> to <dst>`
for ptr<->float, which LLVM rejects. MIR itself is fine: the multi-field unbox declares
`rt_tuple_get` as returning i64 (`switch_operators_calls.spl:5306`) and
`enum_payload_value` F64 arm bitcasts i64 -> f64 (`:661-686`); the `ptr` typing of the
call result comes from the backend's local-type bookkeeping (`fresh_operand_type`).

## Slot encoding (answer)
Raw IEEE-754 bits, not a boxed float.
- Constructor: `box_lowered_enum_tuple_payload` (`switch_operators_calls.spl:6150-6185`)
  stores `encode_declared_enum_payload_slot` (`enum_constructor_payload.spl:577`), which for
  non-u64 calls `bitcast_float_enum_payload` (`switch_operators_calls.spl:716-`):
  f64 -> `bitcast f64 to i64`, f32 -> widen to f64 then bitcast. Then `rt_tuple_set(tuple, idx, i64)`.
- Runtime: `rt_tuple_set/get` are plain word array ops (`src/runtime/simple_core/core_array.spl:490-494`,
  `rt_array_set/get`); no tagging or boxing.
- Decode: `enum_payload_value` F64 arm (`switch_operators_calls.spl:~683`): bitcast i64 -> f64.
So the correct LLVM decode of a `ptr`-typed slot value is `ptrtoint` + `bitcast i64 -> double`.

## Fix
Two new branches in `llvm_bitcast_impl`: ptr -> float = `ptrtoint ptr to iN; bitcast iN to float`,
float -> ptr = `bitcast float to iN; inttoptr iN to ptr` (N = `float_int_equiv`).

## Spec
`test/01_unit/compiler/backend/llvm_bitcast_pointer_bool_spec.spl` (2 new examples).
Fail before the fix, pass after. Note: 4 older examples in that file (the
`emit_bitcast_ir` terminator ones) fail both before and after, unrelated.
