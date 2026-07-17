# Pure-Simple Core Interpreter Dict Literal Dispatch Gap

Date: 2026-07-17
Status: source fixed; execution pending
Severity: P1

## Symptom

The core parser emits `EXPR_DICT_LIT` (tag 25), and a complete dictionary
evaluator existed only in the old `eval_access.spl` split. The live
range-partitioned `eval_expr` rare branch had no dictionary arm, while the
active `_EvalOps/access_literal_assign_eval.spl` owner exported by
`eval_ops.spl` had no `eval_dict_lit`. Every `{}` or `{key: value}` reaching
the pure-Simple tree interpreter therefore fell through to `unsupported
expression kind: DictLit`.

## Root fix

`eval_expr` now routes `EXPR_DICT_LIT` once in its rare branch. The active
`_EvalOps` owner evaluates every key and value, converts keys to the existing
dynamic-field text representation, and returns the established `__dict`
struct. The live index, statement-assignment, and method owners now consume
that same representation; insert/update reuse one value-arena upsert helper.
No new value representation or parallel dispatch was introduced.

## Regression

`src/compiler/10.frontend/core/interpreter/test_interp.spl` now interprets a
nonempty dictionary with computed keys and values plus two empty dictionaries.
The interpreted fixture exercises index read/update, insertion, `set`, `len`,
`keys`, `values`, `contains`, `contains_key`, `get`, and `get_or`. The harness
inspects the resulting `__dict` values and proves that mutating one empty
literal leaves the other empty. The focused source spec pins every live owner
so the implementation cannot drift back into the unused splits.

Execution remains pending under the current no-runtime/no-compiler-command
restriction. `.github/workflows/core-mcp-dev-pipeline.yml` executes
`test_interp.spl`, and `scripts/check/check-bootstrap-portability.shs` enforces
that workflow contract.
