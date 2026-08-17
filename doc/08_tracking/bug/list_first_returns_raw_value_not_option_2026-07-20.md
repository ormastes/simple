# Bug: `List<T>.first` (bare or `()`) returns a raw nilable value, not `Option<T>` as the guide documents

- **Date:** 2026-07-20
- Status: OPEN (P2)
- Status re-verified 2026-08-17 by source inspection (triage shard 02).
- **Area:** `src/compiler_rust/compiler/src/interpreter_method/collections.rs`
  (`"first"` arm, array method dispatch, line ~57), deployed seed at
  `bin/release/x86_64-unknown-linux-gnu/simple`

## Symptom

`generics_spec.spl`, 4 examples compare `list.first` (or a user function that
returns it) against an explicit `Some(x)` enum literal and fail:

```
✗ uses generic function with inference
  fn first<T>(items: List<T>) -> Option<T>: items.first
  expect first([1, 2, 3]) == Some(1)     -->  expected 1 to equal Option::Some(1)

✗ creates generic list
  expect numbers.first == Some(1)        -->  expected 1 to equal Option::Some(1)

✗ defines function returning generic type
  expect make_list(42).first == Some(42) -->  expected 42 to equal Option::Some(42)

✗ implicitly infers type parameters
  expect wrap(10).first == Some(10)      -->  expected 10 to equal Option::Some(10)
```

`doc/07_guide/quick_reference/syntax_quick_reference.md` line 619 documents
`list.first().is_some()` as equivalent to the no-paren `list.first.?` form —
`.is_some()` is an `Option<T>` API method, so the guide's own comparison table
implies `list.first()` (and by the "Ruby-like" no-paren sugar at line 578, bare
`list.first` too) returns `Option<T>`, not a raw nilable value.

## Root cause (confirmed by source read)

`src/compiler_rust/compiler/src/interpreter_method/collections.rs`:
```rust
"first" => arr.first().cloned().unwrap_or(Value::Nil),
```
This returns the raw element or `Value::Nil` directly — never a
`Value::Enum { enum_name: "Option", variant: "Some"|"None", .. }`-tagged value.
This is internally *consistent* with `.?`'s "T? pass-through" contract (which
this pass's earlier fix to `exists_check_spec.spl` confirmed empirically: `.?`
on an already-`Option`-typed value like `Some(42)` unwraps to raw `42`, not
`Some(42)`) — but it contradicts the guide's `list.first().is_some()` ⇔
`list.first.?` equivalence, since a raw nilable value has no `.is_some()`
method at all (it's not an enum).

This is the same "`T?` nilable primitive vs `Option<T>` tagged enum" duality
that shows up repeatedly across this codebase (see MEMORY's recurring
tag-box/enum-payload notes) — here it surfaces as `.first`'s actual runtime
representation not matching its documented one.

## Fix direction (not applied — compiler-internals change, needs rebuild)

Either (a) make `.first`/`.last`/similar array accessors return a proper
`Option<T>`-tagged enum value (matching the guide), and thread that through
callers that currently expect a raw nilable value (e.g. re-verify `.?`'s
pass-through behavior on a real `Option`-returning `.first` doesn't regress),
or (b) fix the guide (`syntax_quick_reference.md` line 619) to state
`list.first` returns a raw nilable `T?`, not `Option<T>`, and drop the
`.is_some()` equivalence claim (replace with an `!= nil` / `.?` example
instead). Given how pervasively `T?` nilable semantics are used elsewhere in
this codebase's own passing specs (confirmed via `exists_check_spec.spl`),
option (b) — fixing the guide, not the runtime — may be the lower-risk fix,
but that decision needs an owner with the full picture of what else relies on
`.first`'s current raw-value behavior.

## Verification

Reproduced at repo tip (2026-07-20) via:
```
bin/release/x86_64-unknown-linux-gnu/simple test test/feature/usage/generics_spec.spl --no-session-daemon
```
Not checked against the pure-Simple self-hosted compiler or a compiled/native
path — only the Rust seed interpreter was probed.

## 2026-08-17 re-verification (lane m1_rust_interp) — LIVE, but do NOT "fix" it as filed

Classified by CONTENT (per session CORRECTIONS #1).

The reported line is confirmed unchanged —
`src/compiler_rust/compiler/src/interpreter_method/collections.rs:139`:

```
"first" => arr.first().cloned().unwrap_or(Value::Nil),
"last"  => arr.last().cloned().unwrap_or(Value::Nil),
```

No `Option` wrap, exactly as filed. **But changing it would be a silent
breaking change, not a fix.** Two things were measured before touching it:

**1. The raw-or-nil contract is deliberate and is contrasted in-source with a
real Option arm.** The `at` arm a few lines below (collections.rs:145+) carries a
comment stating that array `at` was added specifically to provide
`Value::some(elem)` / `Value::none()` bounds-checked access, i.e. the codebase
already made the "return a real Option" decision for a DIFFERENT method and left
`first`/`last` raw on purpose.

**2. The actual builtin-array callers in the tree depend on the RAW contract.**
Of 23 `.first()` sites under `src/`, the ones hitting this builtin arm use
nilable/coalescing forms that an `Option` return would break:

- `src/compiler/99.loader/module_loader.spl:19` — `base.split(".").first() ?? base`
- `src/compiler/99.loader/module_loader.spl:21` — `stem.split("_").first() ?? stem`
- `src/compiler/40.mono/monomorphize/util.spl:112` — `if val first = elems.first():`
- `src/lib/{nogc_async_mut,gc_async_mut}/security/sanitize.spl:53` — interpolated directly

`?? base` against an `Option` would coalesce a `Some(...)` wrapper rather than
the value, turning a correct path into a silent wrong result — the exact defect
class this campaign is hunting. The sites that DO use `.unwrap()` / `.is_some()`
/ `.?` (`core_nogc_immut/static_vec.spl:258`,
`src/app/interpreter/collections/persistent_vec_spec.spl:104,112,250`) are
methods on user-defined `StaticVec`/`PersistentVec` types, not this builtin arm,
so they are unaffected either way.

**Status: reclassified from "interpreter bug" to "documentation mismatch".** The
implementation is the intended one; the doc/`array_ops.spl:308` docstring
(`Array.of([1, 2, 3]).first()  # → Some(&1)`) is what is wrong. Recommended
resolution: correct the documentation to state `first`/`last` return `T?`
(nilable) and point readers at `at(i)` for a real `Option`. If an Option-returning
variant is genuinely wanted, add it additively (e.g. `first_opt`) — do not change
this arm. No interpreter change was made by this lane.
