# parser_intensive_spec: "parses strings with and without interpolation" fails — parser never stamps EXPR_INTERPOLATED_STRING

- **Date:** 2026-08-21
- **Spec:** `test/01_unit/compiler_core/parser_intensive_spec.spl` (39/40; the one failure is `expected 3 to equal 34`)
- **Status:** RESOLVED 2026-08-21 (was: open, pre-existing; not introduced by the grammar-registry cross-check work that surfaced it)

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

## RESOLVED 2026-08-21 — fix option 2 (the spec expectation was wrong)

Decision: the PARSER must NOT stamp `EXPR_INTERPOLATED_STRING`. The pipeline is
built on the opposite contract, stated in
`src/compiler/10.frontend/core/string_interpolation_expand.spl:143-158`: the
driver path "leaves every string literal opaque and sub-parses interpolation
regions much later in the flat->rich bridge (`flat_bridge_build_string_interps`)",
and the promotion helper there deliberately promotes ONLY placeholder-bearing
call arguments so that "the broad StringLit-with-Interpolation-parts
representation the bridge relies on is not disturbed". Stamping tag 34 at parse
time would break that bridge representation for every interpolated literal in
the tree — a large blast radius to satisfy one assertion.

So `parse_expr_src("\"hello {name}!\"")` correctly yields `EXPR_STRING_LIT` (3),
and the spec now asserts 3 with the contract written out inline. No parser
change, therefore **no grammar-registry regeneration**: the registry already
records `EXPR_INTERPOLATED_STRING` as `kind: desugar`-only, which is now exactly
what the spec says too.

Evidence (`bin/simple test test/01_unit/compiler_core/parser_intensive_spec.spl`):

- pre-fix:  `Results: 40 total, 39 passed, 1 failed` (`expected 3 to equal 34`)
- post-fix: `Results: 40 total, 40 passed, 0 failed`

Mirror `test/unit/compiler_core/parser_intensive_spec.spl` updated byte-identical.
