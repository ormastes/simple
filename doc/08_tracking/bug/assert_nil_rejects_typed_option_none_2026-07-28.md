# BUG (FIXED): `assert_nil` rejected a typed `Option::None`; `assert_not_nil` accepted it

- **Filed / fixed:** 2026-07-28
- **Lane:** MATCHER (reported by lane DBDUR, seconded by lane SPECFIX)
- **Severity:** High — rejected a *correct* value, and the mirror matcher passed a
  *wrong* one
- Status: CLOSED (not reproducible)
- Status re-verified 2026-08-17 by source inspection (triage shard 00).

## Symptom

`test/system/database/server/db_server_tier_spec.spl:114`

```
assert_nil(store_read(store, "users", "ghost"))
```

failed on **both** engines with:

```
assert_nil failed: got Option::None
```

The value was correct. `store_read` returns `T?`, and a `T?`-returning function
that does `return nil` yields `Option::None`, not the bare `Value::Nil` literal.
DBDUR had to re-cover two properties in its own spec to work around this.

## Root cause

`nil` has two runtime representations — `Value::Nil` (the bare literal) and
`Option::None` (a `Value::Enum`). `Value::is_nil_like()`
(`src/compiler_rust/compiler/src/value.rs:1120`) is the canonical predicate that
accepts both, and it is what `==`/`!=` against `nil` and the
`expect(x).to_be_nil()` matcher already used.

The `assert_nil` / `assert_not_nil` **seed-interpreter builtins** at
`src/compiler_rust/compiler/src/interpreter_call/bdd.rs:1513` compared against the
bare literal instead:

```rust
"assert_nil"     => if val != Value::Nil { fail }   // rejected Option::None
"assert_not_nil" => if val == Value::Nil { fail }   // ACCEPTED Option::None as "not nil"
```

The second half is the more dangerous one: `assert_not_nil(none)` **passed**, so
the matcher pair could not detect a missing value at all.

Note the builtin shadows the pure-Simple `std.spec` definitions
(`src/lib/nogc_sync_mut/spec.spl:719`, `if value != nil:`) and the test-runner's
injected inline helper (`expect value == nil`) — **both of those were already
correct**, because they go through `==`. Only the Rust builtin was wrong, which is
why the failure text matched `bdd.rs`'s format string exactly.

## Fix

Both arms now use `val.is_nil_like()`. Still strict — this is NOT a truthiness
check: `Some(_)`, `Result::Err`, `false`, `0` and `""` are all non-nil.
`assert_not_nil` also gained the actual value in its failure message.

## Regression coverage

`test/01_unit/lib/spec/nil_matcher_option_none_spec.spl` — 14 examples: both nil
representations accepted, agreement with `== nil` and `expect().to_be_nil()`,
four strictness cases, the `assert_not_nil` mirror, and three trailing examples
that act as the canary for "one failure must not hide the rest of the file".

## Payoff

On `build/matcher_repro/db_server_tier_notransport_spec.spl` (the reporting spec
with only its one hanging `MemoryTransport` example removed, 29 examples):
**23 passed / 6 failed → 28 passed / 1 failed.** Five of the six pre-fix failures
were `assert_nil failed: got Option::None`; all five are green. The remaining
failure is unrelated and pre-existing.

## Not a defect: the runner does NOT abort the file on a failed assertion

DBDUR reported that the runner aborted `db_server_tier_spec.spl` at the failing
line, hiding every later example. That is **not** what a failed matcher does —
verified with `build/matcher_repro/nil_repro_spec.spl`, where the failing
`assert_nil` example is followed by four more that all run and report
(`6 examples, 1 failure`). The observed whole-file loss in that spec was the
**120s file timeout** (`error: test-runner: file timed out`), a separate issue
tracked with the spec itself.
