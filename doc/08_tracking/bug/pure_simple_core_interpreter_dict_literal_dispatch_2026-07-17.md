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
struct used by indexing, assignment, and dictionary methods. No new value
representation or parallel dispatch was introduced.

## Regression

`src/compiler/10.frontend/core/interpreter/test_interp.spl` now interprets a
nonempty dictionary with computed keys and values plus two empty dictionaries.
The harness inspects their established `__dict` representation and proves the
two empty literals received distinct value IDs. The focused source spec pins
the rare-branch ordering and the active `_EvalOps` export so the implementation
cannot drift back into the unused split.

Dictionary indexing, indexed assignment, and dictionary methods remain a
separate known activation gap: their implementations still live only in the
orphaned `eval_access.spl` and `eval_methods.spl` splits. This regression avoids
claiming those consumers work while directly covering literal construction.

Execution remains pending under the current no-runtime/no-compiler-command
restriction. `.github/workflows/core-mcp-dev-pipeline.yml` executes
`test_interp.spl`, and `scripts/check/check-bootstrap-portability.shs` enforces
that workflow contract.
