# `for x in <dict>.values()` — every field read collapses to offset 0 (native codegen)

- **Status:** FIXED 2026-08-24
- **Lane:** U
- **Severity:** blocker — Stage 2 SEGV'd on a 2-line hello world for ANY input
- **Layer:** 50.mir (MIR lowering), NOT 20.hir

## Symptom

Under native codegen only (`bin/simple native-build`; the tree-walk interpreter
was always correct), inside a `for x in d.values():` loop over a
`Dict<K, StructType>`, EVERY field read of the loop variable returned the value
at byte offset 0, typed `i64`.

Minimal reproduce (`test/fixtures/native_dict_values_struct/main.spl`,
struct `P(a: i64, b: text, c: i64)`, `ds[1] = P(a: 7, b: "hi", c: 11)`):

| probe | interpreted | native BEFORE | native AFTER |
|---|---|---|---|
| `values_a` | 7 | 7 | 7 |
| `values_b` | hi | **7** | hi |
| `values_c` | 11 | **7** | 11 |
| `hoisted_b` | hi | **7** | hi |
| `hoisted_c` | 11 | **7** | 11 |
| `keys_k` | kx | kx | kx |
| `textkey_b` | zz | **1** | zz |
| `direct_b` (control, `d[k]`) | hi | hi | hi |
| `array_b` (control, array literal) | hi | hi | hi |

In Stage 2 the same collapse made `func.name` read `func.symbol` as a raw
integer and `func.signature` return nil, so `build_signature` dereferenced a nil
`return_type` -> SIGSEGV. gdb: `build_signature+0x19d`, `mov (%rax)` with
`rax=0`; the `.values()` path emitted `mov (%r12)` + `rt_raw_i64_to_string`
where the correct path emits `mov 0x8(%r15)` + `rt_interp_cstr`.

## Root cause

`lower_for_array_indexed` (`src/compiler/50.mir/mir_lowering_stmts.spl:2738-2771`)
derives the loop variable's struct identity from
`self.array_element_struct_syms[collection_local.id]` and, only when that names a
real struct, sets `self.struct_value_syms[loop_var.id]`. That entry is what lets
`resolve_field_index`
(`src/compiler/50.mir/_MirLowering/function_lowering.spl:1241`) resolve a real
field index; without it the function falls through to its documented fallback at
line ~1305, `0  # Default fallback when type is unknown`, and the field's MIR
type defaults to `MirType.i64()`. Offset 0 + i64 — exactly the observed shape.

Only `lower_array_lit` (`50.mir/_MirLoweringExpr/literals.spl:97`) and the
param-array path ever populated `array_element_struct_syms`. The `.values()` /
`.keys()` arm
(`50.mir/_MirLoweringExpr/method_calls_literals.spl`, the `rt_dict_values` /
`rt_dict_keys` branch) had already been taught — by two earlier bug fixes,
`native_dict_keys_iter_index` and `native_dict_call_result_keys_elem_type` — to
stamp an `Array(elem_type, 0)` MIR type on its result and to normalise
string-shaped element types to `Opaque("str")`. That is why `keys_k` was already
correct. But it never registered the element STRUCT NAME, which is a separate
map, so struct-valued dicts stayed broken.

A second, hidden half: the dict's value type arrives as
`MirTypeKind.Struct(SymbolId)` whose id is MINTED by
`canonical_mir_type_symbol` (`50.mir/_MirLowering/module_lowering.spl`) from
1000000000 up. Those ids exist only in `canonical_type_symbols` —
`symbols.get_symbol_raw` knows nothing about them, so the obvious
`get_symbol_raw(sym).name` lookup returns nil for every canonicalised struct
type. Verified empirically with the `SIMPLE_TRACE_DICT_ELEM=1` probe: the
`Struct(SymbolId(id: 1000000000))` match fired while the name lookup produced
nothing.

## Fix

Two edits, both in the Simple compiler (no `.spl` call site was rewritten —
one fix covers all 89 `.values()` loop sites under `src/compiler/`):

1. `src/compiler/50.mir/_MirLowering/module_lowering.spl` — new
   `me mir_struct_symbol_name(symbol: SymbolId) -> text`: the real symbol table
   first, then a reverse lookup through `canonical_type_symbols`, returning the
   bare name (segment after the last `.`), which is the form `struct_value_syms`
   and `resolve_field_index` are keyed on.
2. `src/compiler/50.mir/_MirLoweringExpr/method_calls_literals.spl` — in the
   `values`/`keys` arm, recover the element struct name from the picked
   key/value MIR type (`Struct(sym)` via the helper above, or `Opaque(name)`),
   explicitly excluding string shapes and `__runtime_array__`, and register it as
   `self.array_element_struct_syms[dict_keys_typed.id]`. This mirrors
   `literals.spl:97` exactly.

The string exclusion is deliberate: unconditionally tagging non-struct elements
is the failure mode already recorded in `lower_for_array_indexed`'s comment
(it corrupted int-array `for`-in sums), so the gate is "a real struct name or
nothing".

## Fence

`sh scripts/check/check-native-dict-values-struct-fields.shs` — drives a real
`native-build` and compares 9 probes, including the two always-correct controls
(`d[k]` direct read, array-literal iteration) so a future "fix" cannot trade one
lane for another. `bin/simple test` CANNOT see this defect: it hard-defaults to
the tree-walk interpreter, which was correct throughout. Neighbours covered by
the same fixture: hoisted `val vs = d.values()`, `.keys()` over a text-keyed
dict, and a `Dict<text, Struct>` (text keys AND struct values).

Interpreter-lane spec (documents the class and pins the interpreter side):
`test/01_unit/language/dict_values_struct_field_native_repro_spec.spl`.
