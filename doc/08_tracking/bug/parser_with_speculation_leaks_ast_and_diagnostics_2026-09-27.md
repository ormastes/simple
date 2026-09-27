# Contextual `with` speculation leaks AST nodes and diagnostics

**Status:** source-confirmed, runtime reproduction pending a source-matched
pure-Simple runner. This is an existing handwritten-parser defect and an
extraction blocker for the canonical scalar grammar/action provider.

## Source path

`src/compiler/10.frontend/core/parser_stmts.spl:902-962` recognizes contextual
`with EXPR as NAME:` by saving lexer and current-token state, consuming `with`,
and calling `parse_expr()` on the remainder. If the resulting root is not a
named cast followed by `:`, it rolls back only `lex_snapshot` and
`parser_tok_save` state, then falls through to ordinary expression parsing.

The speculative `parse_expr()` is effectful. Its constructors append to the
expression arena through `expr_alloc` (`_AstExpr/nodes.spl:515-543`), cast
types can register named types (`parser.spl:949-952`), and malformed input can
append diagnostics through `parser_error` (`parser.spl:392-412`). Neither
`lex_snapshot_rollback` (`lexer.spl:876-880`) nor `parser_tok_restore`
(`parser.spl:1195-1203`) restores those owners. The ordinary parse then runs
again against the restored token stream, leaving abandoned speculative nodes
and possibly an error that the ordinary parse did not produce.

One targeted fixture is a valid ordinary identifier expression such as
`with.move_cursor(1)` in statement position: the speculative parse begins at
`.` after consuming `with`; `parse_primary_expr` reports an unexpected token
(`_ParserPrimary/primary_expr.spl:1107`). The code then restores tokens but
retains that diagnostic. `with + 1` likewise creates speculative expression
nodes before fallback. These fixtures need execution on a source-matched
pure-Simple runtime before claiming observed output or exact arena growth.

## Required correction

Make failed alternatives discard every speculative AST/type/module/diagnostic
effect as well as lexer and current-token state. A checkpoint must cover owner
arenas and pending declarations, or the parser must perform a side-effect-free
lookahead before building an expression. Do not merely decrement the expression
count: `expr_alloc` appends to parallel arrays, and a count-only reset leaves
stale entries at the reused index. Keep the accepted `with EXPR as NAME:`
semantics and ordinary identifier use, including nested expressions and
recovery ordering.

## Acceptance

1. `with.move_cursor(1)` and `with + 1` parse as ordinary identifier
   expressions with no speculative diagnostics or orphan AST nodes.
2. Accepted `with R.open() as r:` still desugars to the existing resource
   closing path, including early exits; retain
   `test/01_unit/compiler/resource/resource_with_scoped_spec.spl` coverage.
3. Malformed `with` forms report only diagnostics from the chosen parse path.
4. Repeated rejected alternatives do not grow retained AST, type, module, or
   diagnostic state beyond the committed parse result.
5. Differential legacy/canonical snapshots include these cases and prove
   source-ordered effects and rollback parity before canonical admission.

The direct checkpoint survey in
`doc/01_research/local/canonical_simple_parser_effect_inventory_2026-09-27.md`
identifies this confirmed checkpoint site in which `parse_expr()` runs before
a possible rollback. Other parser side-effect paths still require
the full semantic review recorded in the rule survey.
