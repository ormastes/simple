# compiler_schema registry generator drops every comma-listed enum variant after the first

- **Filed:** 2026-08-23
- **Status:** IMPLEMENTED, UNVERIFIED — verification was explicitly skipped
- **Severity:** HIGH — silently understates the contract surface, so gates built on it are blind
- **Generator:** `src/app/compiler_schema/`
- **Artifact:** `spec/compiler_schema/registry/compiler.mir.MirTypeKind.sdn`

## Summary

`enum MirTypeKind` (`src/compiler/50.mir/mir_types.spl:135`) declares **36**
variants. The generated registry records **29 rows**, but three of those rows
are malformed combined identities. Ten independent variant identities are
absent; seven are the non-first tokens:

`I16`, `I32`, `I64`, `U16`, `U32`, `U64`, `F64`

which is exactly the set of variants appearing as the 2nd..4th token of a
comma-separated declaration line:

```
    I8, I16, I32, I64
    U8, U16, U32, U64
    F32, F64
```

`I8`, `U8` and `F32` — the first tokens — occur only inside malformed IDs such
as `MirTypeKind.I8, I16, I32, I64`; they are not valid independent rows either.
The repair replaces three malformed rows with ten valid rows, a net increase of
seven. The generator reads one declaration row per line instead of one variant.

## Why this matters

The registry is the declared producer universe for the transition tables in
`spec/compiler_schema/transitions/`. `mir_inst_to_llvm.sdn` states its universe
is "enumerated from the generated registry". So a backend that silently dropped
`I32` or `F64` would be invisible to the schema freshness gate, because those
variants are not in the universe the gate compares against. A contract surface
that under-reports itself cannot ratchet the part it under-reports.

`compiler.mir.MirInstKind.sdn` (126) and `compiler.mir.MirTerminator.sdn` (9)
agree with the code, because those enums declare one variant per line. The defect
is latent wherever an enum uses the comma-list form — this needs a repo-wide
sweep, not just a `MirTypeKind` patch.

## Reproduce

```sh
grep -c 'spl:variant@compiler.mir.MirTypeKind\.' spec/compiler_schema/registry/compiler.mir.MirTypeKind.sdn   # 29
# code declares 36; see doc/09_report/mir_construct_census.json
```

## Fix direction

Split on `,` after stripping comments when parsing an enum body, then re-run
`bin/simple run src/app/compiler_schema/main.spl generate` and re-check every
generated registry, not only this one.

## Implementation (2026-08-25)

`extract_enum_variants` now splits each normalized declaration with linear
passes, recognizing commas only at parenthesis/bracket depth zero. Multi-line
declarations accumulate trimmed line parts and join once; normalization gathers
maximal non-whitespace spans and also joins once, avoiding the former repeated
growth and rescan of the whole buffer. This preserves payload commas and handles
a comma list whose first variant has a multi-line payload. Focused coverage
exercises comments, simple comma lists, multi-line payloads, payload commas, and
a trailing variant on the same line.

The mechanically affected authoritative output is
`compiler.mir.MirTypeKind.sdn`: its count is now 36, with three malformed rows
replaced by ten independent rows. `index.sdn` records 378, the sum of the twelve
included registry counts after that replacement. Other generator drift was
deliberately excluded from this bug fix. No tests, builds, benchmarks, SPipe,
optimizer, or manual verification were run per user instruction.
