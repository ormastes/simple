# Seed JIT: a local holding a bool-result lambda is typed `bool`, truncating the closure pointer (2026-11-12)

Status: FIXED (`mir::closure_call_types` retypes the closure-holding local slot to I64; test `local_holding_a_bool_result_closure_is_pointer_sized`). Was live on `release/1.0.0`; no fallback, no diagnostic.

## Repro

```simple
fn main():
    val f = \x: x > 1
    val r = f(2)
    print "r={r}"                 # expect r=true -> SIGSEGV (core dumped)
```

```simple
fn main():
    val xs = [1, 2, 3]
    val big = \x: x > 1
    print "{xs.map(big)},{xs.filter(big)}"   # expect [false, true, true],[2, 3] -> prints [],[]
```

Both run under the JIT. The same lambda written inline
(`xs.filter(\x: x > 1)`) is correct.

## Cause (read from the Cranelift IR, not yet fixed)

HIR types a `Lambda` expression as its BODY type, so the local `f` is typed
`bool`. Codegen declares that local as `i8` and stores the closure handle
through it:

```
v2 = call fn1(v0, v1)     ; closure handle
v4 = ireduce.i8 v2        ; truncated to 8 bits
v7 = sextend.i64 v4
v8 = call fn2(v7)         ; rt_closure_func_ptr(garbage) -> NULL
```

The call then jumps to 0 (crash), or a runtime consumer sees a non-closure
and yields an empty result. `mir::closure_call_types` already retypes the
`Store`/`Load` of a closure-holding local to I64, but the LOCAL's declared type
(and so its stack slot) stays `bool`.

## Suggested fix

Give a local that is bound to a closure the pointer type: either in the same
pass (rewrite `function.locals[i].ty` for every local in `closure_locals`), or
at MIR `Let` lowering when the initializer is `HirExprKind::Lambda`. f64-result
lambdas work today only because their slot is already 64 bits wide.
