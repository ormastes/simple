# class_field_array_dict_bracket_reads_native_unsafe_2026-11-06

**Priority:** P2 · **Status:** fix-implemented-verification-pending ·
**Ratchet:** `scripts/check/check-class-field-dict-bracket-read.shs`

## Premise

Native `self.<f>[k]` bracket reads on a class field declared `Dict<K, [V]>`
were reported to mis-read (SEGV / AV) because the field-projection temp is
builder-typed with the erased `Dict(K, i64)`, so the dict index read took
`decode_runtime_value`'s integer arm (`rt_value_as_int_wide` for i64,
`raw >> 3` for narrower kinds) on an array handle. 209 such sites were
baselined as a ratchet on 2026-11-06; PR #7634 (2026-11-07) extended the
HIR-value-type refinement in `expr_dispatch.spl` (`lower_index` dict path)
from Bool to Array, landed WAIT_VERIFY with no executed evidence.

## 2026-11-09 MIR-level investigation

`test/01_unit/compiler/50.mir/class_field_array_dict_index_read_spec.spl`
lowers source through the real frontend -> HIR -> MIR pipeline and inspects
the method's instruction stream: the read must contain the `rt_dict_get`
call and NO integer decode (`Shr` binop or `rt_value_as_int_wide` call).
A scalar `Dict<i64, i64>` field is the positive control (integer decode
present) and a local `[i64]` index is the element-decode control.

Shapes checked (all lower to the array passthrough on release/1.0.0 tip
`91fecec397f`): `Dict<>` and brace-shorthand `{K: [V]}` fields, `fn` and
`me` methods, text and i64 keys, i64/text/struct element types, insert
followed by same-scope typed readback (the documented 2026-08-08 native
repro), nested key expression `self.d[s.id]` (the #7170 call-site shape),
constructor with `{}` literal, `contains` guard, `for v in self.d[k]`, and
`self.d[k][0]`.

Result: **green for every shape both WITH and WITHOUT the #7634 hunk** (the
Array alternative in the condition at `expr_dispatch.spl:2985` was reverted
to Bool-only for the red attempt). For these shapes `value_type_from_hir`
already resolves `V = [T]` before the refinement, so the #7634 branch is not
reached. No MIR-level red could be produced on the current tip.

Consequences:

- The MIR index lowering is correct for class-field array-valued Dict reads
  as far as the MIR instruction stream shows; the spec pins that contract.
- The native crash, if it still reproduces, is NOT in the dict-value decode
  selection. The remaining suspects are backend-side (LLVM/Cranelift handling
  of the passthrough `Copy` of an array handle, or the field-projection
  load), which cannot be verified on this lane (no native run).
- The 4 real new call sites that grew the ratchet (`fields_of_class`,
  `struct_field_type_ownership_key`, `points`, `edges`) were migrated to
  `.get(k) ?? []`. The other 5 "new" hits were `self.effects[...]` on a plain
  array / `Dict<Symbol, EffectTag>`, swept in because
  `hir_ownership_facts.spl` added an array-valued Dict field named `effects`;
  the ratchet now matches field names per file, so those are gone.

## Verification plan (native, pending)

1. `bin/simple native-build test/fixtures/compiler/class_field_array_dict/main.spl`
   (the #7634 fixture, 21 checks) on Linux x86_64 LLVM and Cranelift; expect
   `CLASS_FIELD_ARRAY_DICT_PASS|checks=21`.
2. If it crashes: the MIR is already array-typed (this spec), so bisect the
   backend lowering of `MirInstKind.Copy` on `Array` results of
   `rt_dict_get`, not `expr_dispatch.spl`.
3. On pass: retire the ratchet (delete script + baseline) and migrate
   nothing further — `.get(k) ?? []` and `self.f[k]` are then equivalent.
