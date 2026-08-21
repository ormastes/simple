# A multi-line lambda body is never executed — collection builtins silently get the wrong answer

- **Date:** 2026-08-21
- **Status:** RESOLVED 2026-08-21 (fix + RED-first spec landed; evidence at
  the bottom of this file)
- **Found by:** fixing `map_for_each_missing_on_dict_2026-08-21.md` — the dict
  `for_each` arm was implemented, dispatched correctly, and still did nothing
- **Binaries:** reproduces identically on the deployed seed `bin/simple` AND on
  a freshly rebuilt seed, so it is **pre-existing** and independent of that fix

## Symptom

A lambda argument whose body is written on following indented lines is parsed,
accepted, and then **never run**. The call does not fail — it returns a value
that looks plausible, so the caller proceeds on a wrong answer with no
diagnostic of any kind.

```simple
fn main():
    val m = {1: 10, 2: 20}

    val single = m.filter(\k, v: v > 15)
    print("single_line={single.len()}")      # 1   <- correct

    val multi = m.filter(\k, v:
        v > 15
    )
    print("multiline={multi.len()}")         # 2   <- WRONG, predicate never ran
main()
```

```
SIMPLE_EXECUTION_MODE=interpreter bin/simple run fixture.spl
single_line_filter=1
multiline_filter=2
```

The multi-line form keeps **every** entry, because the predicate's value is
not the predicate's result.

## Root cause

Two correct-in-isolation behaviours compose into a silent wrong answer:

1. `parse_lambda_body` (`src/compiler_rust/parser/src/expressions/helpers.rs:707`)
   parses an indented lambda body into `Expr::DoBlock(statements)`. A
   single-line body stays an ordinary expression. This is why the two forms
   diverge at all.

2. Evaluating an `Expr::DoBlock` as an expression
   (`src/compiler_rust/compiler/src/interpreter/expr/control.rs:296`) yields
   `Value::BlockClosure { nodes, env }` — a *reified, unforced* block. It does
   not execute the statements.

The collection helpers
(`src/compiler_rust/compiler/src/interpreter_helpers/collections.rs`) call
`evaluate_expr(body, ...)` and use the result directly. So for a multi-line
body they receive a `BlockClosure`, and:

- `filter` tests it for truthiness. `Value::BlockClosure` sits in the
  always-truthy arm of `Value::truthy()`
  (`compiler/src/value_impl.rs`), so **every element passes** — a
  filter that silently becomes the identity function.
- `map`/`map_values` would store the closure itself as the mapped value.
- a side-effecting body performs **no** side effects at all.

Nothing anywhere forces the block, and nothing reports that it was not forced.

## Why this is worse than a crash

Every failure mode here is a *wrong result*, not an error:

| form | expected | actual |
|---|---|---|
| `filter` multi-line predicate | matching subset | **all** elements |
| `map` multi-line body | mapped values | closure objects |
| side-effecting multi-line body | effects applied | **nothing happens** |

A multi-line lambda is the natural way to write anything non-trivial, so the
more complex the predicate, the more likely it is to be silently ignored.

## Scope

Confirmed for dict `filter`. By inspection the same
`evaluate_expr(body, ...)`-and-use-the-result shape is used by the whole
lambda-taking family in `interpreter_helpers/collections.rs`
(`eval_dict_filter`, `eval_dict_map_values`, `eval_array_filter`,
`eval_array_map`, `eval_array_find`, `eval_array_any`, `eval_array_all`,
`eval_array_reduce`, and the option helpers). The exact per-method blast
radius has **not** been enumerated — do that as the first step of the fix
rather than trusting this paragraph.

`dict.for_each`/`each` is the one member already fixed: `eval_dict_for_each`
matches `Expr::DoBlock`/`Expr::UnsafeBlock` and executes the statements with
`exec_node` against the caller's env. That is a local patch at one call site,
deliberately **not** generalised here, because the right fix is shared.

## Fix sketch

Add one shared helper — "evaluate a lambda BODY", as opposed to evaluating an
arbitrary expression — that forces a `DoBlock`/`UnsafeBlock` (executing its
statements and yielding the last value) and evaluates anything else normally,
then route every lambda-invoking collection helper through it. Doing it once,
centrally, is the point: the defect exists because each helper independently
assumed `evaluate_expr` was enough.

Note that a *pure* helper (`filter`, `map`) needs the block's **value**, while
a side-effecting one (`for_each`) needs its **effects on the caller's scope**;
the helper should return the value and take the env to run in, so both are
served without a second parallel rule.

## Reproduce fixture

`test/01_unit/lib/nogc_sync_mut/map_for_each_spec.spl` covers the `for_each`
half that is fixed. A spec for the still-broken `filter`/`map` half is NOT
added here, because per `.claude/rules/testing.md` it would be a correct spec
asserting behaviour the implementation does not have — it belongs with the
fix, and this record is the file:line + unblock condition it points at.

## Unblock condition

Implement the shared lambda-body forcing helper above, route the collection
helpers through it, then add the RED-first spec for multi-line `filter`/`map`
predicates alongside it.


## Resolution 2026-08-21

**Fix.** One shared helper, exactly as the sketch above required, rather than a
patch per method:
`src/compiler_rust/compiler/src/interpreter_helpers/lambda_body.rs`
(new) — `eval_lambda_body(body, env, ..)` forces an `Expr::DoBlock` /
`Expr::UnsafeBlock` body through `interpreter::block_exec::exec_block_fn`
against the environment the caller already prepared (so a side-effecting body
reaches the caller's scope) and yields the block's last value (so a pure
predicate gets its result); anything else falls through to `evaluate_expr`
unchanged. A `return` inside the body propagates out of the enclosing function
via the existing `CompileError::TryError` early-return channel, the same one
if/match expression arms use — otherwise it would silently become the body's
value.

Routed through it (`evaluate_expr(body, ..)` -> `eval_lambda_body(body, ..)`):
- `interpreter_helpers/collections.rs` — 7 call sites, covering
  `eval_array_filter`, `eval_array_find`, `eval_array_any`, `eval_array_all`,
  `eval_array_reduce`, `eval_dict_filter`, `eval_dict_map_values` and the
  option/result helpers that share those bodies.
- `interpreter_helpers/args.rs` — `apply_lambda_to_vec`, which is what
  `eval_array_map` actually uses.
- Exported as `interpreter_helpers::eval_lambda_body`
  (`interpreter_helpers/mod.rs`).

`eval_dict_for_each`'s existing local `exec_node` loop is deliberately LEFT in
place: it must run against the CALLER's env with the parameter names saved and
restored around the traversal, which is a stronger contract than the shared
helper's, and it is already correct and covered by
`test/01_unit/lib/nogc_sync_mut/map_for_each_spec.spl`.

**Spec (RED-first).**
`test/01_unit/lib/nogc_sync_mut/multiline_lambda_body_spec.spl`, mirrored to
`test/unit/lib/nogc_sync_mut/multiline_lambda_body_spec.spl`. 8 examples,
each pairing the single-line form with the multi-line form so a future
regression cannot hide by breaking both consistently: array
`filter`/`map`/`any`/`all`/`find`/`reduce`, dict `filter`/`map_values`.

| binary | result |
|---|---|
| deployed seed `bin/simple` (pre-fix) | `8 total, 1 passed, 7 failed` |
| seed rebuilt with this fix | `8 total, 8 passed, 0 failed` |

(`map_values` passes pre-fix because that example asserts only the entry
count, which the identity-closure bug preserves; the other seven discriminate.)
