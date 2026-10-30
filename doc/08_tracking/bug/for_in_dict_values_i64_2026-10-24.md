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
