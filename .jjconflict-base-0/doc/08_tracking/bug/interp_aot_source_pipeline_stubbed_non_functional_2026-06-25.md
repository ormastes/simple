# interp: AOT source-compile pipeline stubbed / non-functional under seed interpreter

- **id**: interp_aot_source_pipeline_stubbed_non_functional_2026-06-25
- **status**: OPEN (partial fix landed)
- **severity**: P2 (feature gap, not a crash on its own)
- **date**: 2026-06-25

## Summary

`bin/simple run src/compiler/80.driver/main.spl -c <file> --target wasm32 -o out.wat`
(the pure-Simple compiler driver under the Rust seed interpreter) cannot emit a
real module for non-bootstrap sources. The wasm backend itself is proven
(`wasm_compile_spec` 37/37); the blockage is upstream in the driver's HIR/MIR
lowering, which is stubbed for all non-bootstrap sources.

## Chain of defects

1. **parse_full_frontend nil-return** — `parse_full_frontend(...) -> Module`
   (`src/compiler/10.frontend/frontend.spl`) had no return statement; the last
   expression was `desugar_collections(...)` (returns nil). Every non-bootstrap
   `ctx.modules[*]` was nil → "accessing field 'functions' on nil".
   **FIXED**: added trailing `module` return (this change landed).

2. **HIR lowering stubbed** — `lower_and_check_impl()` in
   `src/compiler/80.driver/driver.spl` (the `sources.len() > 0` branch) gives only
   the bootstrap entry real HIR lowering; every other source gets an empty
   `HirModule(functions: {})`. NOT fixed (un-stub reverted, see below).

3. **MIR lowering stubbed** — `lower_to_mir()` in
   `src/compiler/80.driver/driver_pipeline.spl` (`sources.len() > 0` branch)
   stubs non-bootstrap sources to empty `MirModule(functions: {})`. NOT fixed.

## Why the un-stubs were reverted

Un-stubbing HIR+MIR (fresh lowering per source) is the correct direction, but it
immediately exposes an unbounded chain of interpreted-compiler bugs:

- **4a — Option.map on a present value**: interpreter represents `Some(x)` as the
  bare value `x`; it has no Some-fallback for Option methods, so
  `fn_.return_type.map(...)` (hir_lowering/_Items/declaration_lowering.spl:150) errors
  "method 'map' not found on type 'Type'". (Already worked around at the callsite
  with an explicit `.?` check; other callsites remain exposed.)
- **4b — resolve.spl method orphaning**: `class MethodResolver`
  (`src/compiler/35.semantics/resolve.spl`) has two indent-0 free functions
  (`create_trait_solver_for_resolution`, `create_method_resolver`) between the
  class fields and its `me` methods; the dedent closes the class, so methods
  177+ get absorbed into `create_method_resolver`'s body → `resolve_module`
  fails on nil. Pre-existing structural bug.
- **typed-optional nil field-access SIGSEGV** — see
  `interp_typed_optional_nil_field_access_sigsegv_2026-06-25.md`.

## Decision (cautious consolidation)

Per the "go with caution — it is made crash" directive, keep only the
contract-correct parse fix (#1) and document #2/#3/#4 as concrete bugs. The
HIR/MIR un-stubs and the seed Some-fallback prototype were reverted/stashed to
keep the seed at baseline (zero seed risk). `--check` exits 0 clean with the
parse fix alone.

## Repro

```bash
SEED=src/compiler_rust/target/bootstrap/simple
$SEED run src/compiler/80.driver/main.spl -c /tmp/hello.spl --target wasm32 -o /tmp/w.wat
# before parse fix: "accessing field 'functions' on nil"
# after parse fix:  reaches HIR/MIR stub -> empty module
```
