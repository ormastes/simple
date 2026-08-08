# JIT HIR lowering: cannot infer struct-typed field type (falls back to interpreter)

- **Date:** 2026-07-18
- **Status:** open
- **Severity:** low (correctness unaffected — interpreter fallback runs; JIT coverage lost)
- **Area:** compiler JIT / HIR lowering

## Symptom

Running a spec whose `main` constructs a struct that itself contains a
struct-typed field:

```
[INFO] JIT compilation failed, falling back to interpreter:
HIR lowering error: Unsupported feature: cannot infer field type while
lowering main: struct NeChip field geometry
```

## Repro

`timeout 300 bin/simple run src/lib/hardware/nand_emu/test/module_import_spec.spl`
on the 2026-07-18 seed. `NeChip` (src/lib/hardware/nand_emu/chip.spl) holds a
`geometry: NeGeometry` field (plain struct-in-struct, no generics); HIR
lowering of the spec `main` fails to infer the field type and the whole file
drops to the interpreter.

## Expected

Struct-typed fields are ordinary composition (the repo's mandated pattern —
no inheritance); JIT lowering should infer them like scalar fields.

## Notes

Interpreter results are correct; all nand_emu specs pass on the fallback
path. Cost is JIT speed only. Not blocking nand_emu work.
