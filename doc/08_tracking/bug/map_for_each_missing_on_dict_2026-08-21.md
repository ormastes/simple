# `Map.for_each` is not implemented on `dict` (array-only builtin)

- **Status:** OPEN
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
