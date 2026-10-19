# Top-level `while a = inc(a)` fast path writes a local copy (result stays 0)

- **Date:** 2026-10-19
- **Status:** OPEN — being fixed on branch `work/interp-toplevel-while-fastpath`
- **Severity:** high (silent wrong result in the seed interpreter)
- **Found by:** work/interp-coverage-conditions (overhead benchmark)

## Repro (seed `60f58dd3…`, also base `5983f64f…`, coverage OFF)

```simple
fn inc(x: i64) -> i64:
    x + 1
fn f() -> i64:
    var acc = 0
    var i = 0
    while i < 5:
        acc = inc(acc)
        i = i + 1
    acc
var a = 0
var i = 0
while i < 5:
    a = inc(a)
    i = i + 1
print("top={a} in-fn={f()}")   # prints top=0 in-fn=5
```

Same result with `return x + 1`. With `SIMPLE_COVERAGE=1` the top-level
loop gives the correct 5.

## Cause (suspected)

`try_exec_one_arg_int_helper_while_loop` (`interpreter_control.rs` ~2043 /
~2084) reads the target and index with `env.get` and writes them back with
`env.insert`. At module top level those names are module globals, so the
write lands in the local env and the later read sees the stale global.

## Why the coverage gate does not catch it

`scripts/check/check-hash-algos-coverage.shs` runs with coverage ON, and
coverage ON skips every `while`/`for` shape fast path (they would bypass
the probes inside the loop body). The gate therefore never exercises this
path; it needs its own coverage-off spec.

## Related coverage-tool limitations (not this defect; recorded here)

- `expr_site_sub` (`interpreter/coverage_helpers.rs:235-240`) keys an
  if-expression / standalone `and`/`or` site by the enclosing function plus a
  hash of `format!("{:?}", expr)`, so two textually identical such
  expressions in one function share one site: the denominator undercounts.
- A lambda takes no anchor of its own (`execute_function_body` only swaps
  `FN_ANCHOR` for functions with a module owner), so a lambda body run from
  another function inherits that caller's `FN_ANCHOR` and file; its
  expression-level sites then don't match the statically registered ones.
