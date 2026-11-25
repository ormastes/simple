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

## Verification 2026-11-25 (P3 fleet, release/1.0.0) — STALE, symptom gone

Ran the doc's own repro on the current tracked self-hosted binary
(Windows, `SIMPLE_LIB=src bin/simple.exe`):

```
bin/simple.exe run src/lib/hardware/nand_emu/test/module_import_spec.spl
```

Result: exit 0, every example passes (edc, badblock, fault, chip,
rtl.pin_frontend — "constructs an S1 chip carrying the resolved geometry ✓"),
and `grep -c 'JIT compilation failed\|jit-fallback'` on the full log = 0.
The struct-in-struct field-type inference failure no longer fires on the
named repro. The original report was against the 2026-07-18 Rust seed;
whatever fixed it has since landed in the self-hosted lane.

**Status:** RESOLVED (repro clean 2026-11-25; no jit-fallback emitted).

Verification base note: runs above executed at tree fcd95d41d60 (release/1.0.0
at session start) with its matching tracked bin/simple.exe. Later same-day
merges (notably cfd89933699, the 940-annotation `@representation_boundary`
autofix) moved src/ ahead of the pinned binary, which then rejects the new
decorator; the verified behavior is unchanged by that source-only annotation
wave.
