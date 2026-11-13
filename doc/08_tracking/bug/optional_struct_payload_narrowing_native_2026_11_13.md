# optional_struct_payload_narrowing_native_2026_11_13

Status: FIXED in the compiler (MIR call-argument lowering). The fix takes
effect only in code produced by a compiler that contains it, so the generator
`@workaround` in `src/app/compiler_schema/fold_gen.spl` stays until a fixed
Stage 2 has rebuilt itself.

## Symptom
```
fn enc(node: E) -> i64          # E is a struct
fn payload_arg(t: TK) -> i64:   # enum TK: Arr(text, E?)
    match t:
        case Arr(_, sz):
            if sz == nil:
                return -1
            return enc(sz)      # implicit E? -> E after the nil guard
```
| lane | Some(E(..))-built `E?` | bare-built `E?` |
|---|---|---|
| seed interpreter | correct | correct |
| seed JIT | wrong value (`extras.len()` ~2.6e17) | correct |
| run-26 Stage 2 candidate (pure-Simple native) | SIGSEGV in the callee | SIGSEGV in the callee |

An explicit unwrap (`sz!`, `if val s = sz`) is correct on every lane. The
interpreter is right, so the source is right: this is a miscompile.

In the compiler, this shape is the generated AST semantic encoder
(`ast_semantic_encode_expr(b_Array_f1, state)`). A `[T; <int literal>]`
struct field is the only producer of a non-nil `TypeKind.Array` size
(`flat_field_sized_type`, af589940249), so every HIR worker that reached one
died: doc/08_tracking/bug/2026-11-13_stage2_surface_projection_segv_intlit_array_size.md.

## Root cause
MIR has no flow typing. The nil-check narrowing is recorded only in the type
checker (`30.types/type_infer/inference_expr.spl` ~150-190), and
`context.spl lookup_with_narrowing` returns a narrowed type without writing
it back into HIR. After the guard, `sz` still has type `Optional(E)` and, on
the pure-Simple native lane, holds the canonical Option box whether it was
built bare (`ensure_option_handle`) or with `Some(...)` (`rt_enum_new`). The
enum-payload binder keeps the raw slot
(`decode_declared_enum_payload_slot`).

Call arguments unwrapped only scalar optionals (`option_scalar_payload_of`):
- free functions: `lower_call_with_value` in
  `50.mir/_MirLoweringExpr/switch_operators_calls.spl`
- methods: `lower_method_call_arg` in `50.mir/mir_lowering_stmts.spl`

A struct or class parameter received the box, and the callee read the box
header as the record. This is the call-argument twin of
mir_optional_record_receiver_reads_option_box_2026-10-25.md, which fixed field
reads only.

## Fix
`option_record_argument_payload_v1(arg, local, declared)`
(`method_calls_literals.spl`). When the parameter is declared `Named(S)` and
the argument's optional payload names the same symbol S, it delegates to
`option_record_receiver_payload_v1`, which emits `rt_unwrap_or_self` for a
struct or class with a known layout. Both call-argument sites call it from a
`HirTypeKind.Named` arm.
- A parameter declared `T?` keeps the box.
- A plain record argument is unchanged.
- A None argument unwraps to nil and still faults in the callee, as a raw nil
  did, so no nil is widened.

## Evidence
- MIR, seed interpreter:
  `test/01_unit/compiler/mir/optional_record_argument_unwrap_spec.spl`.
  - Red on release/1.0.0 f46955a55c5: 1/2, no `rt_unwrap_or_self` at the
    call arguments.
  - Green with the fix: 2/2.
- Native: `test/01_unit/compiler/codegen/native_optional_record_argument_unwrap_spec.spl`
  embeds the end-to-end program.
  - Red on the run-26 candidate (2f9dedc191f9) via the scratch harness: SIGSEGV after `BEGIN`.
  - Seed interpreter output: `BEGIN 4096 4095 -1 100007 9 -1 END`.
  - Native green needs a Stage 2 that contains this fix.

## Remove the workaround when
A Stage 2 built from a tree that contains this fix runs the native spec
green. Then drop the `optional_struct_payload_narrowing_native_2026_11_13`
`@workaround` in fold_gen.spl, regenerate, and keep the projection only
where the scalar `as`-cast rule (ERR-01) needs it.
