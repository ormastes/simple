# Bug: Self-Hosted Parser Cannot Parse Lambda Expressions in Call Arguments

**Date:** 2026-06-11  
**ID:** selfhosted_parser_lambda_gap_2026-06-11  
**Severity:** HIGH — blocks E-PAR-006 share-nothing lint from firing in self-hosted lane

## Symptom

All closure/lambda forms that produce `EXPR_LAMBDA` nodes fail to parse when used as
call arguments in the self-hosted parser. Tested forms and results:

| Form | Parser result |
|------|--------------|
| `green_spawn(\x: x + 1)` | `parser_error: kind 191 '\'` — backslash not recognised in expression position |
| `green_spawn(\: counter)` | same backslash error |
| `green_spawn(fn(): val x = 1)` | `parser_error: kind 20 'fn'` — fn keyword not recognised as expression in call arg |
| `green_spawn({ counter })` | parse error on `{` |
| `green_spawn(do: counter)` | **parses** but yields `EXPR_DO_BLOCK` (tag 44), NOT `EXPR_LAMBDA` (tag 26) |

## Affected Fixtures

- `test/fixtures/concurrency_api_misuse/green_spawn_shared_var_capture.spl`  
  Uses `\x: expr` form → parse errors → lint never runs on it.

## Impact on E-PAR-006 Self-Hosted Lane

`check_concurrency_share_nothing` (src/compiler/35.semantics/lint/concurrency_share_nothing.spl)
gates its lambda check on `expr_get_tag(first_arg) == EXPR_LAMBDA`. Since no parseable
closure form in call-argument position produces `EXPR_LAMBDA`, the lint's E-PAR-006
violation path **cannot fire** through the self-hosted parser. The lint logic is correct;
the parser is missing the lambda-in-expression production.

## Suspected Area

`src/compiler/10.frontend/core/` parser expression rules — the primary expression
parser (`parse_primary` / expression descent) does not handle:
- `\` as start of a lambda expression
- `fn` keyword as an anonymous function expression (only as top-level declaration)

## Resolution Required

Add lambda expression parsing so `\params: body` and `fn(params): body` are valid
primary expressions (usable as call arguments). Until fixed, all E-PAR-006 end-to-end
green tests that use lambda syntax are blocked in interpreter/self-hosted mode.
