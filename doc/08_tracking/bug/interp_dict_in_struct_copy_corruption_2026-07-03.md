# Interpreter: Dict values corrupted inside struct under copy-return semantics

**Date:** 2026-07-03
**Severity:** high (silent data corruption)
**Status:** open — workaround in use

## Symptom

A `Dict<text, i64>` embedded in a **struct** returns corrupted values when the
struct is passed through copy-return (value-semantics) functions. Probe:

```simple
struct Box:
    data: Dict<text, i64>

fn box_set(b: Box, k: text, v: i64) -> Box:
    var nb = b
    nb.data[k] = v
    nb
```

Stored `42` reads back `336`; stored `7` reads back `56` — a consistent 8x
scaling artifact, suggesting a pointer/width confusion when the Dict is copied
as part of the struct value.

## Not affected

`class Sheet` with `cells: Dict<text, Cell>` works — classes use mutation
(reference) semantics, so the Dict is never value-copied.

## Workaround (in production use)

Parallel arrays instead of Dict-in-struct where copy semantics are required:
`src/app/office/sheets/cell_format.spl` (`SheetFormats { keys: [text],
specs: [FormatSpec] }` with linear scan). Same idiom as `[CondRule]` in
`cond_format.spl`.

## Related known issues

- Struct default-field omission corrupts all field reads in interpreter mode
  (found during array-formula work, 2026-07-03).
- Same-name struct in two modules collides in the global registry.
- Aggregates through function params lose mutations (return-the-object rule).

## Next step

Reproduce in a minimal interpreter test (`Dict` copy path in
`src/app/interpreter/` value cloning); the 8x factor points at element-size
(byte-vs-slot) confusion when cloning Dict storage embedded in a struct value.
