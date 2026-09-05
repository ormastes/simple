# Phase-2 parse process-sharding: blocked on a missing AST serialization boundary (2026-08-21)

## Goal
Make `native-build --entry-closure ... --threads N` shard the serial per-file
`phase2:parse` loop across N worker PROCESSES (the seed interpreter is not
thread-safe on this path). Stage 1 currently spends 20-50 s/file x 656 files.

## What `--threads` actually reaches today
- CLI parse: `src/app/io/_CliCompile/compile_targets.spl:891-907` -> exports
  `SIMPLE_NATIVE_BUILD_THREADS` (`:1131`).
- Sole consumer: `src/compiler/80.driver/driver_aot_native_output.spl:129`
  (`driver_native_build_threads()`), used once at `:860` as `num_threads` on the
  native CODEGEN/LINK job.
- Phase 2 never reads it. The parse loop is
  `src/compiler/80.driver/driver_source_pipeline_parsing.spl:360-420`
  (`for source in unique_entry_sources: parse_full_frontend(...)`), strictly
  serial by construction.

## Why the proposed shard design cannot be built "minimally"
The design requires children to hand parsed modules back to the parent. There is
no serialized form for a parsed module anywhere in the tree:

- `parse_full_frontend` (`src/compiler/10.frontend/frontend.spl:69-96`) returns an
  in-memory `ParserModule` and nothing else. Results live only in
  `ctx.modules` / `module_surfaces`.
- `ParserModule` (`src/compiler/10.frontend/parser_types.spl:21`) is ~25
  collections of rich AST types. `parser_types.spl` + `parser_types_expr.spl`
  declare **72 struct/enum/class types** with **148+ enum variants** in the expr
  half alone.
- `src/compiler/80.driver/smf_serialization.spl` serializes only
  `*_placeholder` records - `serialize_function_placeholder` etc. are
  SIGNATURE-level. No body, no `Expr`/`Stmt`/`Pattern`/`Type` encoder, and no
  decoder at all in the reverse direction.
- `flat_ast_bridge` (`src/compiler/10.frontend/_FlatAstBridge/`, 3382 lines) is
  one-directional (core flat AST -> `ParserModule`); the flat AST is not exposed
  or persisted by `parse_and_build_module_scoped`.
- The SMF manifest path (`driver_api_interpret.spl:28-73`) loads a whole-program
  `.smf` in `CompileMode.SmfExec`. It is not a per-module AST re-entry point, so
  it cannot be used to hand 656 shard results back into one link unit.
- `spec/compiler_schema/registry/*.sdn` + `src/app/compiler_schema/{visitor,fold}_gen.spl`
  cover KIND enums (variant names) only - no field-level schema, so a serializer
  cannot be generated from it as-is.

Estimated real cost of the missing piece: a round-trip `ParserModule`
encoder+decoder over 72 types / ~190 variants, i.e. several thousand lines, where
every omitted field is a SILENT miscompile of the bootstrap compiler. That is not
a minimal change and must not be landed under time pressure.

## Feasible sequencing (proposal, not implemented)
1. **Fix the per-file cost** (seed-interpreter work already in flight). At
   ~1 s/file the 656-file phase is ~11 min and sharding is not needed.
2. If sharding is still wanted, land the boundary FIRST as its own change:
   extend `spec/compiler_schema/registry/` to field-level schemas and generate
   `parser_module_codec.spl` (encode+decode) from it, gated by a
   parse-reparse-equality spec over the whole `src/app` closure
   (`encode(parse(f))` must equal `encode(decode(encode(parse(f))))` for all 656
   files) before any shard mode is wired.
3. Only then add `--parse-shard i/N` to `src/app/cli/native_build_worker.spl`
   plus a parent fan-out in `driver_source_pipeline_parsing.spl`
   (deterministic sorted-path round-robin, merge in path order, child non-zero =
   loud failure naming the file + child stderr, `--threads 1` = current path).

## Status
Not implemented. No `src/` file changed by this investigation.
