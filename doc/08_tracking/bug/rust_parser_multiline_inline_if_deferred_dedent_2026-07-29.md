# Rust parser leaves a deferred Dedent after a multiline inline `if`

- **ID:** `rust_parser_multiline_inline_if_deferred_dedent`
- **Status:** SOURCE FIXED — focused regression passes; refreshed Stage2/RV64 pending
- **Severity:** P1

## Symptom

RV64 attempt 18 reached
`src/lib/skia/feature/shaper/ot_layout_apply.spl:37:1` and failed with
`Unexpected token: expected expression, found Dedent`.

The preceding function contains a multiline condition with an inline body:

```simple
if kind < 1u32 or kind > 8u32 or kind == 7u32 or offset < 8 or
    target < subtable or target + 2 > limit: return None
```

The binary parser records the continuation indent. Block-form `if` already
drained that deferred layout, but inline statement/expression branches did not.
The continuation Dedent therefore closed the function early and left its real
Dedent at module scope.

## Fix and regression

Inline bodies now consume only the recorded deferred continuation Dedents.
The shared `parse_inline_or_block` owner covers inline `elif`/`else if`
statement branches, and the inline-expression helper covers recursive
`elif`/`else if` branches. One focused parser regression exercises multiline
conditions in statement and expression forms, optional branches, a multiline
final expression, and the following sibling-function boundary.

RV64 attempt 18 exited 1 after 25.02 seconds with no ELF. A fresh seed, Stage2,
and RV64 build remain the production closure gate.
