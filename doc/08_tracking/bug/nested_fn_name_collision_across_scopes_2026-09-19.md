# BUG: two nested `fn`s with the same name in different scopes collide, and the second call runs the first one's closure

- **id:** nested_fn_name_collision_across_scopes_2026-09-19
- **status:** OPEN, isolated with a 20-line repro, not yet fixed
- **severity:** P2 — a LOUD error, never a silent wrong answer (established below, and it is the reason this is P2 and not P1)
- **found:** 2026-09-19, while re-measuring a supposedly-open item in
  `nested_fn_in_spec_block_loses_captured_local_2026-08-04`

## Symptom

Two nested `fn`s that happen to share a name, declared in **different** enclosing
scopes, are registered into the same flat `functions` map keyed by the bare name.
The second call resolves to the first one's closure, whose captured scope is gone
by then, and fails:

```
semantic: variable `base` not found
```

The enclosing function is correct in isolation. It breaks only because something
*else*, somewhere else in the file, declared a nested `fn` of the same name first.

## Minimal repro

Both examples are individually correct; run together, B fails.

```simple
use std.spec

fn helper_scope() -> i64:
    val base = 10
    fn fact(n: i64) -> i64:
        if n <= 1:
            return base
        n * fact(n - 1)
    fact(4)

describe "two nested fns with the same name in different scopes":
    it "A: declares its own fact inside the it block":
        val base = 10
        fn fact(n: i64) -> i64:
            if n <= 1:
                return base
            n * fact(n - 1)
        expect(fact(4)).to_equal(240)

    it "B: calls the module-level helper whose nested fact has the same name":
        expect(helper_scope()).to_equal(240)
```

```
Results: 2 total, 1 passed, 1 failed
    semantic: variable `base` not found
```

## The name is the whole cause — proven by changing only the name

The identical file with the helper's inner `fn` renamed to
`uniquely_named_fact` (same body, same structure, same call order) passes:

```
Results: 2 total, 2 passed, 0 failed
```

Nothing else differs. That is the control, and it is what makes this a
collision rather than a scoping bug in either function on its own.

## It is LOUD, not silent — probed specifically

The obvious fear is a silent wrong answer: the wrong closure runs, resolves
everything, and returns a plausible number. Probed directly with two same-named
nested fns whose bodies reference the same identifier so that both *could*
resolve:

```simple
fn scope_b() -> i64:
    val k = 100
    fn compute(n: i64) -> i64:
        n + k
    compute(1)                 # expect 101

# ... and inside an `it` block, a different `compute` with `val k = 1`
```

Result on both the deployed binary and one built from current source:
`semantic: variable 'k' not found` — an error, not `2` returned where `101` was
expected. The winning closure's captured environment belongs to an `it` block
that has already completed, so its locals are unreachable and the lookup fails
rather than silently finding the wrong `k`.

**This is why the severity is P2.** A silent wrong answer here would be P1. The
failure is always visible, and it names a variable that is plainly in scope at
the source location the reader is looking at — confusing, but never quiet.

## Where it comes from

`exec_block_closure_into` (`interpreter_call/block_execution.rs`, `Node::Function`
arm) registers a nested `fn` **twice**: in the flat `functions: HashMap<String,
Arc<FunctionDef>>` so the body can recurse, and in the block scope as a closure
over the block's locals. The flat map is keyed by the **bare name**, with no
scope qualifier, so the second registration of `fact` overwrites — or is
overwritten by — the first, and the two are indistinguishable afterwards.

The dispatch fix landed on 2026-09-19 for
`nested_fn_in_spec_block_loses_captured_local_2026-08-04` prefers the env binding
over the flat entry, but **only when the two are the same `Arc`**
(`Arc::ptr_eq`). That test was deliberately pointer identity rather than an
emptiness check, and it is exactly right for the single-definition case. On a
collision the two are *different* `Arc`s, so the check correctly declines and
dispatch falls through to the flat map — which holds the other scope's closure.

## Candidate fix, not yet attempted

In the same dispatch ladder: when the environment holds a `Value::Function`
binding for the name and the flat-map entry is a **different** `Arc`, prefer the
environment binding anyway. A lexically visible nested `fn` should shadow a stale
flat-map entry left by an unrelated scope; the flat map is a recursion aid, not a
namespace.

Two things to check before believing that:

- it must not break recursion — inside a converted body the letrec binding puts
  the fn under its own name in the captured env, so an env-first rule finds the
  right one;
- it must not shadow a genuine module-level function — the condition requires the
  env binding to *be* a `Value::Function`, so a same-named local non-function
  value does not trigger it.

The real repair is a scope-qualified key for the flat map, which is a larger
change and should be weighed against just removing the double registration now
that the env binding carries recursion.

## Related

- `nested_fn_in_spec_block_loses_captured_local_2026-08-04` — the parent defect;
  this was found while re-measuring its "remaining lane split" item, which turned
  out to be closed. The module-scope shape it described as still failing fails
  **only** in the presence of a colliding name, which is what that record's
  repro file happened to contain.
- `duplicate_impl_method_definitions_silent_first_wins_2026-08-08` — the same
  first-wins-on-a-bare-name class, one layer up. It is also why hoisting nested
  fns to module scope was rejected when fixing the JIT lowering: the hoist would
  have created exactly this collision at a layer where it *could* be silent.
