# MIR: `for (i, v) in arr.enumerate()` binds a struct element without a by-value copy

- **Date:** 2026-11-05
- **Status:** fixed (2026-11-05)
- **Severity:** P2 (aliasing, value-semantics violation)
- **Area:** `src/compiler/50.mir/` for-in lowering (enumerate path)

## Defect

Structs are value types (Bug #177, `maybe_copy_struct_value`): a by-value binding
that reads a struct handle out of container storage must copy. The dict-pair loop
`for (k, v) in dict` over struct values does copy (GetField indices `[0, 1, 0, 1, 1]`
in `test/01_unit/compiler/50.mir/for_in_runtime_tuple_decode_spec.spl`). The
enumerate path `for (i, v) in arr.enumerate()` emits the same tuple slot shape
without the copy (`[0, 1, 1]`). So `v` aliases the array's element storage, and a
write to `v.field` inside the loop body leaks into the array.

## Evidence

Found in review of lane-3 MIR fixes, 2026-11-04. Both helpers store the container's
struct handle (pointer-represented) in the native tuple slot. The dict-pair copy was
present at 5120e296997 (2026-10-21) and absent at 9dd0197d4e8 (2026-10-12). The exact
commit is unattributed; 9e55c23dd16 is the most plausible.

## Fix direction

Apply the same `maybe_copy_struct_value` by-value copy to the enumerate element
binding, and add a spec that mutates `v.field` in the loop and asserts the array
element is unchanged.

## Root cause and fix (2026-11-05)

`maybe_copy_struct_value` (`src/compiler/50.mir/mir_lowering_stmts.spl`) only
copied when the init local's MIR type was `Struct(sym)`. The enumerate pair slot
is built as `Opaque(owner)` (`builtin_method_extras.spl`, `enumerate` branch), so
the copy was skipped. Plain `for p in arr` (`lower_for_array_indexed`) never
called it at all, so it aliased array storage too (GetField `[1]`, no copy).

Fix: `maybe_copy_struct_value` resolves `Opaque(name)` (when equal to the struct
name) to its symbol; `lower_for_array_indexed` copies the element binding via
`maybe_copy_struct_value(loop_var, fesn, true)` when the element has a real
struct owner. Classes and primitives are untouched (class check inside the helper).

Perf: one record copy (malloc) per iteration, only for struct elements; tracked in `for_loop_struct_copy_per_iteration_alloc_2026-11-05.md`.

Evidence: `for_in_runtime_tuple_decode_spec.spl` RED (3 failures: `[0,1,1]`,
`[0,1]`, `[1]`) then GREEN (15/15): enumerate now `[0,1,0,1,1]`, mutation case
`[0,1,0,1]`, plain-for `[0,1,1]`. The pre-existing enumerate pin `[0,1,1]` encoded
the bug and was updated.
Runtime check: `test/01_unit/language/for_loop_struct_element_by_value_spec.spl` (3/3 on the seed interpreter).
