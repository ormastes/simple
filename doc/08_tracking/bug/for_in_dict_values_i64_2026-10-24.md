# for-in over `Dict.values()` lowers with collection MIR type I64 (2026-10-24)

**Status:** open

Symptom (run-12, plugins.backend_vhdl.vhdl.vhdl_call_lowering):
`for-in over non-array iterables is not supported by native codegen yet (#143); iterate an array or use while (collection mir type: I64)`.

Sites: `for x in self.active_local_names.values()` and
`for x in self.active_hardware_call_instance_names.values()` (Dict<i64, text> fields).
In that module the receiver method types are still unresolved at MIR lowering (see the
missing impl-module imports fixed in the same change), so `.values()` yields an untyped I64.

Workaround: bind `.values()` to a typed `[text]` local and iterate it. Tagged
`@workaround bug=for_in_dict_values_i64_2026-10-24`.

Compiler gap (open): MIR for-in should type `Dict<K,V>.values()` as `[V]` from the declared
field type instead of falling to I64 when the receiver call is not resolved.

## Compiler fix (2026-11-05, mirp2-C)
`for_collection_declared_type` (src/compiler/50.mir/mir_lowering_stmts.spl) now
recovers `[V]`/`[K]` for an argless `.values()`/`.keys()` iterable whose HIR call
carries no array type, from the receiver's declared `Dict<K, V>` via
`receiver_declared_type` (locals + field chains). The erased-word collection then
takes the indexed-array lane instead of #143. Specs:
test/01_unit/compiler/50.mir/for_in_dict_values_typed_spec.spl (3 cases, pass).
Gap: the original cross-module unresolved-receiver shape is not reproduced in a
single-file unit fixture (HIR already stamps the type there); the workaround in
vhdl_call_lowering stays until a native re-run of that module confirms. Status
remains open pending that confirmation.
