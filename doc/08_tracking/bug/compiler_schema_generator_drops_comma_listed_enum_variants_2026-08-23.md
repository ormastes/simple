# compiler_schema registry generator drops every comma-listed enum variant after the first

- **Filed:** 2026-08-23
- **Status:** OPEN — not repaired (`src/app/compiler_schema/**` is outside this lane's scope)
- **Severity:** HIGH — silently understates the contract surface, so gates built on it are blind
- **Generator:** `src/app/compiler_schema/`
- **Artifact:** `spec/compiler_schema/registry/compiler.mir.MirTypeKind.sdn`

## Summary

`enum MirTypeKind` (`src/compiler/50.mir/mir_types.spl:135`) declares **36**
variants. The generated registry records **29**. The 7 missing are exactly:

`I16`, `I32`, `I64`, `U16`, `U32`, `U64`, `F64`

which is exactly the set of variants appearing as the 2nd..4th token of a
comma-separated declaration line:

```
    I8, I16, I32, I64
    U8, U16, U32, U64
    F32, F64
```

`I8`, `U8` and `F32` — the FIRST token of each line — are present. Every
non-first token is absent. The generator reads one variant per line.

## Why this matters

The registry is the declared producer universe for the transition tables in
`spec/compiler_schema/transitions/`. `mir_inst_to_llvm.sdn` states its universe
is "enumerated from the generated registry". So a backend that silently dropped
`I32` or `F64` would be invisible to the schema freshness gate, because those
variants are not in the universe the gate compares against. A contract surface
that under-reports itself cannot ratchet the part it under-reports.

`compiler.mir.MirInstKind.sdn` (126) and `compiler.mir.MirTerminator.sdn` (7)
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
