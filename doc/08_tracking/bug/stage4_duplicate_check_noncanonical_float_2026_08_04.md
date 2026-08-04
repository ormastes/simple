# Stage 4 duplicate checker uses unresolved `float` conversion

## Status

Open; next x86 Phase 4 blocker retained on 2026-08-04.

## Symptom

The final bounded Phase 4 cycle parsed all 1,351 surfaces and crossed the CLI
lint, CLI handler, and leak-check repairs. HIR lowering then reported four
`unresolved name: float` diagnostics in
`src/compiler/tools/duplicate_check/main.spl`.

## Exact sites

- similarity threshold positional option;
- similarity threshold `--name=value` option;
- semantic threshold positional option;
- semantic threshold `--name=value` option.

## Next action

In a fresh bounded session, reproduce the four conversions with a focused
duplicate-check native contract, identify the canonical text-to-`f64` owner,
replace only the non-canonical conversions, and retain threshold parsing and
invalid-input behavior. Do not widen HIR resolution or add a runtime alias.
