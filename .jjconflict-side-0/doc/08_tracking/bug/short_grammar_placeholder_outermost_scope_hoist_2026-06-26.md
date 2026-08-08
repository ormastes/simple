# Bug: `_1` placeholder lambda hoists to the outermost expression in nested calls

- **ID:** short_grammar_placeholder_outermost_scope_hoist_2026-06-26
- **Found:** 2026-06-26
- **Severity:** P2 — silently wrong results; any `_N` placeholder used inside an inner call argument captures the whole surrounding expression
- **Category:** Compiler / short-grammar placeholder / lambda scoping
- **Status:** OPEN (worked around in `json_coverage_spec` by using explicit `\x:` lambdas)

## Summary

The `_1`/`_N` placeholder short-grammar desugars an implicit lambda by binding
it to the **outermost** enclosing expression rather than the innermost call
whose argument position contains the placeholder. When a placeholder predicate
is written directly as a call argument that is itself nested inside another
call, the generated lambda swallows the outer call.

## Repro

```spl
val arr = json_array([json_number(1)])
expect(json_array_find(arr, json_to_number(_1) == 9)).to_be_nil()
```

Intended desugaring (placeholder scoped to `json_array_find`'s 2nd arg):

```spl
expect(json_array_find(arr, \x: json_to_number(x) == 9)).to_be_nil()
# json_array_find returns nil (no element == 9) → assertion passes
```

Actual desugaring (placeholder hoisted to the outermost expression):

```spl
\x: expect(json_array_find(arr, json_to_number(x) == 9)).to_be_nil()
# the whole expect(...) becomes a lambda body
```

So `expect(...)` receives a **lambda** as its actual value:

```
✗ returns nil when array find misses
    expected <lambda> to be nil
```

Same failure shape for `json_array_every(arr, json_to_number(_1) > 1)`,
`json_array_some(arr, json_to_number(_1) == 2)`, and
`json_array_group_by(arr, json_to_string(json_object_get(_1, "kind")))`.

## Workaround

Write the predicate as an explicit lambda (`\x: ...`) instead of a placeholder.
Confirmed: the explicit form scopes correctly and returns the real result.

## Fix direction

Placeholder-lambda transformation should bind the synthesized lambda at the
**nearest enclosing call argument** boundary, not the statement/outermost
expression. Likely the same transform used by `parse_pipe`
(`transform_placeholder_lambda`, see
[[short_grammar_pipe_placeholder_parentheses_2026-05-27]]) but applied to
ordinary call arguments with the correct (innermost) scope. Seed-level — takes
effect after a self-hosted rebuild/bootstrap.

## Related

- `short_grammar_pipe_placeholder_parentheses_2026-05-27` (pipe RHS placeholder, fixed)
- `short_grammar_placeholder_value_binding_interpreter_2026-05-27` (stale)
