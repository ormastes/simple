# MIR: `for (i, v) in arr.enumerate()` binds a struct element without a by-value copy

- **Date:** 2026-11-05
- **Status:** open
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
