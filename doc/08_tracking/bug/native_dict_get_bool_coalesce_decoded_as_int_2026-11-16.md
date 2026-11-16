# `{K: bool}.get(k) ?? false` decodes the hit as an int (false reads true)

- Found: 2026-11-16, Stage 3 self-build (r16, integ2 Stage 2 objects).
- Status: MIR source fixed on `work/bool-dict-get-coalesce-decode-20261116`;
  takes effect in native code after the next Stage 2 rebuild.
- Spec: `test/01_unit/compiler/mir/dict_get_bool_coalesce_decode_spec.spl`.

## Symptom

Stage 3 MIR rejected every `MirOperandKind.Const(MirConstValue.X(..), ..)`
with `enum construction '...MirOperandKind::Const': payload type mismatch at 0`
(mir_data, io_passes, var_reassign_ssa, collection_opt_core,
auto_vectorize_codegen).

## Cause

`lower_dict_runtime_read` (`src/compiler/50.mir/_MirLoweringExpr/expr_dispatch.spl`)
returns the raw `rt_dict_get` word for a `d.get(k)` whose value type is bool,
but it did not record the read's `bool?` HIR type, unlike every other
`d.get(k)` arm. `??` then found no Option inner type, merged as the erased
i64, and decoded the hit with `rt_value_as_int_wide`. The tagged false word is
19 and `19 >> 3 = 2`, so a stored `false` reads back as true.

In Stage 3 this hit `declared_enum_constructor_owner`
(`src/compiler/20.hir/hir_lowering/_Expressions/declared_enum_constructor.spl:19`,
`generic_enum_constructor_owners.get(owner.id) ?? false`): every enum read as
generic, the function returned -1, no declared enum constructor became an
`EnumLit`, and MIR took `lower_enum_construct_named`, which records no type for
a nested constructor payload. Proven under gdb on r16: forcing the branch at
that site turns every `mir_named` hit into `mir_enumlit` and the fixture
compiles cleanly.

Not the #6953 discriminant class: `rt_enum_check_variant` on the resolution
passed.

## Evidence (integ2 Stage 2, cranelift, native run)

| form | result |
|---|---|
| `d.get(k) ?? false`, stored false (local, field, text key) | FAIL (true) |
| `if val v = d.get(k)`, stored false | FAIL (true) |
| `d[k]`, stored false | ok |
| `{i64: i64}` control | ok |

The seed interpreter passes every row.

## Workaround

`d[k]` after `contains_key` (Stage 3 lane branch
`work/stage3-payload-const-wa-20261116`). `if val v = d.get(k)` on a bool dict
was also wrong natively; the spec does not pin it, so whether this fix covers
it is unverified (open).
