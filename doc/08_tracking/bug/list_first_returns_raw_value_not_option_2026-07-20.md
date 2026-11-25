# Bug: `List<T>.first` (bare or `()`) returns a raw nilable value, not `Option<T>` as the guide documents

- **Date:** 2026-07-20
- **Status:** open (found triaging `test/feature/usage/generics_spec.spl`)
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

## Resolution 2026-11-25 (p2w3-ah lane, release/1.0.0) — FIXED via option (b), guide aligned to the recorded owner decision

The open question this doc left ("option (a) change the runtime vs option (b)
fix the guide ... needs an owner with the full picture") is settled by a
recorded owner decision: `src/compiler_rust/compiler/src/interpreter_method/
collections.rs` (array `get` arm comment) cites **owner decision 2026-11-09,
`array_get_contract_drift_crypto_2026-10-18`: `a.get(i)` returns `T?` on EVERY
lane** — the raw-nilable contract is the decided one, so option (b) applies.

Behavior re-confirmed on release/1.0.0 HEAD with the pinned seed,
`SIMPLE_EXECUTION_MODE=interpreter` (the evaluator `bin/simple test` uses):
`[1,2,3].first == 1` true, `[1,2,3].first == nil` false, `[].first == nil`
true — a raw nilable value, never an `Option` tag. The generic-fn shape from
the spec (`fn first<T>(items: List<T>) -> T?: items.first`) was probed the
same way: returns the raw element, `== nil` on empty.

Changes landed:

1. `doc/07_guide/quick_reference/syntax_quick_reference.md` — the
   "Refactoring Patterns" row claiming `list.first().is_some()` ⇔
   `list.first.?` is corrected to `list.first != nil` ⇔ `list.first.?`, with
   an explicit note that `.first`/`.last` return raw `T?` and have no
   `.is_some()`; the "No-Paren Method Calls" section gained the same
   one-sentence contract note.
2. `test/feature/usage/generics_spec.spl` — the four examples that asserted
   the pre-decision `Option<T>` contract (`expect ....first == Some(x)`) now
   assert the decided `T?` contract (`== x`), and the one
   `fn first<T>(...) -> Option<T>` signature returning `items.first` is now
   `-> T?`. This is aligning the spec with the recorded owner decision, not
   weakening it: the new assertions are the strict equality oracles for the
   decided contract, each verified by an equivalent interpreter probe on this
   host (g1-g4 all true; `-> T?` signature accepted, empty case `== nil`).

**Verification limit:** the spec file itself was not executed —
`bin/simple test` is repo-wide blocked at this HEAD (pinned seed rejects
`@representation_boundary`, added by cfd89933699) and this lane may not
rebuild the seed. Each changed assertion was verified individually via
`bin/simple run` interpreter probes replicating the exact spec bodies. A
follow-up lane with a working test runner should re-run
`test/feature/usage/generics_spec.spl` end to end.
