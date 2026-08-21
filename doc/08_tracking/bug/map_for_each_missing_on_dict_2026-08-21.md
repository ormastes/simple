# `Map.for_each` is not implemented on `dict` (array-only builtin)

- **Status:** RESOLVED 2026-08-21 (seed-side; evidence at the bottom of this record)
- **Found:** 2026-08-21, triaging `test/01_unit/lib/nogc_sync_mut/map_traversal_spec.spl`
- **Failing spec:** `test/01_unit/lib/nogc_sync_mut/map_traversal_spec.spl`
  - `Results: 4 total, 3 passed, 1 failed`
  - `✗ visits each entry exactly once`
  - `semantic: method `for_each` not found on type `dict` (receiver value: {1: 1, 2: 2})`

## What happens

```simple
var map: Map<i64, i64> = Map.new()
map.insert(1, 1)
map.insert(2, 2)
map.for_each(\key, value:
    total = total + value
)
```

`Map` lowers to the builtin `dict`. Sibling examples in the same spec
(`merge`, key/value collection) pass, so this is not a `Map` lowering problem —
it is a single missing method.

## Root cause

`for_each` is registered **only for arrays**. The two places that know the name
are both array-scoped:

- `src/compiler_rust/compiler/src/codegen/llvm/functions.rs:2965`
  `("Array" | "array", "each") | ("Array" | "array", "for_each") => Some("rt_array_each")`
- `src/compiler_rust/parser/src/expressions/postfix.rs:81` (name is merely
  recognised as a closure-taking postfix method)

There is no `dict` arm anywhere. Dict methods are dispatched from the seed
interpreter's dict method table (see the mutating-method list at
`src/compiler_rust/interpreter_helpers/patterns.rs:1128`, which enumerates
`set/insert/remove/delete/merge/extend/clear` — no traversal method at all).

## Why it was not fixed in this pass

The gap is in the **Rust seed**, not in `.spl`: adding `for_each` needs a dict
arm in the interpreter method table plus the matching codegen arm, and a
bootstrap redeploy to take effect. A bootstrap was at Stage 3 and a 16-way test
sweep was running, so neither `bin/simple build bootstrap` nor a redeploy of
`bin/release/x86_64-unknown-linux-gnu/simple` was permissible.

The failing example is left **failing on purpose** — it is not skipped,
disabled, or deleted.

## Fix sketch

Add a `dict`/`Map` arm for `each`/`for_each` alongside the existing array arm,
passing `(key, value)` to the closure, and dispatch it in the interpreter's
dict method table. Iteration order should match the existing dict key
iteration order so the new method agrees with `for k in map:`.

## Re-confirmed seed-only 2026-08-21

Checked for a pure-Simple place to close this instead: there is none.
`/usr/bin/grep -rn '"merge"|"map_values"|"for_each"' src/compiler/95.interp`
returns **zero** hits — the pure-Simple interpreter layer has no dict method
table at all, and the `method 'for_each' not found on type 'dict'` text is not
produced anywhere under `src/compiler/**`. `Map` in `src/lib` is not a class
with methods either (`src/lib/nogc_sync_mut/src/map.spl` lowers to the builtin
`dict`), so a stdlib-side `for_each` has nothing to attach to. The fix stays
where the record says: the seed's dict method table plus the codegen arm, then
a redeploy. Unchanged; still OPEN.


## RESOLVED 2026-08-21 — fix applied

**Fix, three parts** (all in `src/compiler_rust`):

1. **Dispatch arm.** `compiler/src/interpreter_method/collections.rs`,
   `handle_dict_methods`: added `"for_each" | "each"` alongside the existing
   `filter` / `map_values` arms. `each` is accepted as the alias so the dict
   surface matches the array arm in `codegen/llvm/functions.rs:2965`.

2. **Traversal helper.** `compiler/src/interpreter_helpers/collections.rs`,
   new `eval_dict_for_each`, re-exported through
   `interpreter_helpers/mod.rs` and `interpreter/mod.rs`. Iterates
   `dict_entries_sorted` — the SAME order as `for (k, v) in dict`, `keys()`,
   `values()` and `entries()`, as the fix sketch above required — and recovers
   keys through `dict_entry_key_for_iteration`, so a composite key arrives as
   the original value rather than the internal map string.

3. **Two defects the sketch did not anticipate**, each of which would have
   left the method present but useless:

   - *The accumulator.* `filter`/`map_values` evaluate the lambda against a
     CLONE of its captured env, which is right for a pure transform and fatal
     for `for_each`: the canonical use is `total = total + v`, and a cloned
     env discards exactly that. `eval_dict_for_each` instead runs the body
     against the CALLER's env, binding the parameters for the duration of each
     entry and restoring them afterwards (on the error path too), so the loop
     variables cannot leak into the caller's scope. Covered by the
     "accumulates into a variable of the enclosing scope" and "does not leak
     its loop variables" examples.
   - *The multi-line lambda body.* A multi-line lambda body parses to
     `Expr::DoBlock`, and evaluating a `DoBlock` as an expression yields an
     unforced `Value::BlockClosure` (`interpreter/expr/control.rs:296`)
     instead of running it — so the body's statements never execute. The
     helper matches `Expr::DoBlock`/`UnsafeBlock` and executes the statements
     with `exec_node` directly. **This is a symptom of a broader, separate,
     pre-existing defect** — see the note at the end of this record.

**Regression spec:** `test/01_unit/lib/nogc_sync_mut/map_for_each_spec.spl`
(mirrored to `test/unit/lib/nogc_sync_mut/`). 8 examples: visits-each-once,
accumulator survives, key+value passed, `each` alias, order agrees with
`keys()`, no loop-variable leak, receiver unchanged, empty-map no-op.

**Evidence:**

| spec | deployed seed (pre-fix) | rebuilt seed (post-fix) |
|---|---|---|
| `map_for_each_spec.spl` (new) | `8 total, 0 passed, 8 failed` | `8 total, 8 passed, 0 failed` |
| `map_traversal_spec.spl` (the originally failing spec) | `4 total, 3 passed, 1 failed` | `4 total, 4 passed, 0 failed` |

The originally reported example, `✗ visits each entry exactly once`, is green.

**Note on the key's type.** The key reaches the lambda in the same
representation `keys()` and `entries()` use — for a scalar `i64` key that is
its text form, not an `i64` (`m.keys()` likewise yields `"1"`, so `k + 1`
concatenates). That is a pre-existing property of the whole dict surface, not
something this change introduced; the spec asserts it as-is so `for_each`
cannot silently drift away from its sibling accessors.

**Separate defect found while fixing this — NOT fixed here.** Evaluating a
multi-line lambda body as an expression yields an unforced
`Value::BlockClosure`, which is *truthy*. `for_each` was rescued by executing
the block directly, but every OTHER lambda-taking collection builtin still
takes the unforced value at face value, so a multi-line predicate silently
does the wrong thing rather than failing:

```simple
val m = {1: 10, 2: 20}
m.filter(\k, v: v > 15)        # -> 1 entry   (correct)
m.filter(\k, v:
    v > 15
)                              # -> 2 entries (WRONG: predicate never ran)
```

Reproduces identically on the deployed seed and on the rebuilt one, so it is
pre-existing and independent of this change. It affects the whole
`filter`/`map`/`any`/`all` family and produces wrong ANSWERS with no
diagnostic. Filed as
`doc/08_tracking/bug/multiline_lambda_body_unforced_blockclosure_2026-08-21.md`.
