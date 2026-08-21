# parser_intensive_spec: "parses strings with and without interpolation" fails — parser never stamps EXPR_INTERPOLATED_STRING

- **Date:** 2026-08-21
- **Spec:** `test/01_unit/compiler_core/parser_intensive_spec.spl` (39/40; the one failure is `expected 3 to equal 34`)
- **Status:** open, pre-existing (not introduced by the grammar-registry cross-check work that surfaced it)

## What the spec asserts
`parse_expr_src("\"hello {name}!\"")` must yield tag `EXPR_INTERPOLATED_STRING` (34). It yields `EXPR_STRING_LIT` (3).

## Evidence that this predates the grammar work
- `git grep -n "expr_interpolated_string(" HEAD -- src/compiler/10.frontend/core` (excluding the constructor itself): **0 callers**. No production under `core/**` has stamped tag 34 at any point in the current tree; the only producer is the desugar pass `src/compiler/10.frontend/desugar/placeholder_lambda.spl` (`replace_placeholders*` via `expr_interpolated_string_with_text`), which runs after parsing.
- The grammar registry (`spec/compiler_schema/registry/compiler.frontend.Grammar.sdn`) now records exactly this: `EXPR_INTERPOLATED_STRING` is produced only by `kind: desugar` rows.
- `string_interpolation_expand.spl` rewrites `{...}` parts of an `EXPR_STRING_LIT` in a later pass, so an expression parsed in isolation keeps tag 3.

## Fix options
1. Make the parser stamp `EXPR_INTERPOLATED_STRING` when a string literal contains an unescaped `{` (then `string_interpolation_expand` consumes tag 34 instead of sniffing `EXPR_STRING_LIT` with `expr_get_int == 0`), or
2. Change the spec to run the expansion pass before asserting, if "parsed in isolation keeps tag 3" is the intended contract.

Either way the registry will reflect it automatically (a parser production would then produce tag 34 and the desugar row would stay).
