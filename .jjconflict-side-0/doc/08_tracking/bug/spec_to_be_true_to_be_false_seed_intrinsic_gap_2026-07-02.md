# Bug: `expect(x).to_be_true()` / `.to_be_false()` fail with "method not found on type bool"

**Status:** PARTIALLY FIXED (Rust seed source patched; rebuild/deploy verification pending)
**Date:** 2026-07-02
**Severity:** Medium (two documented BDD matchers are unusable under `bin/simple test`/`run`)

## Summary

`ExpectHelper` (`src/lib/nogc_sync_mut/spec.spl:527-541`) defines
`to_be_true`/`to_be_false`/`to_be_nil`/`to_be_truthy` as ordinary class
methods, all added together in commit `97a9358`. At runtime, `to_equal`,
`to_be_nil`, `to_be_truthy`, and `to_contain` all resolve correctly, but:

```
expect(true).to_be_true()
```

fails with:

```
semantic: method `to_be_true` not found on type `bool` (receiver value: true)
```

Repro (reproduced): a spec with `to_be_true`, `to_be_false`, `to_be_truthy`,
`to_be_nil` cases under `timeout 120 bin/simple test <file>` — only the
first two failed.

## Root Cause

`bin/release/x86_64-unknown-linux-gnu/simple` (the binary `bin/simple`
resolves to) is currently **not** the pure-Simple self-hosted compiler — it
is built directly from the Rust seed at `src/compiler_rust` (confirmed via
`strings`: the binary embeds debug paths under
`src/compiler_rust/.../interpreter_method/mod.rs` and literal matcher
strings "to be truthy"/"to be falsy"/"to be nil"/"to contain"/"to equal" —
with no "to be true"/"to be false" strings present at all). This matches the
"emergency stopgap" state called out in `.claude/rules/bootstrap.md`
("Reverting bin/simple to the seed is an emergency stopgap only").

In the seed, `expect(value)` is special-cased in
`src/compiler_rust/compiler/src/interpreter_call/bdd.rs` (`"expect" =>` arm,
~line 757): it does **not** instantiate an `ExpectHelper` object. It just
returns the evaluated raw value (e.g. `Value::Bool(true)`) so a `.to_*()`
chain has something to dispatch on.

The chained `.to_*()` call is then intercepted as an intrinsic directly on
that raw value in
`src/compiler_rust/compiler/src/interpreter_method/mod.rs`
(`evaluate_method_call`, ~line 226). A hardcoded match list recognizes
`to_equal`, `to_be`, `to_contain`, `to_be_truthy`, `to_be_falsy`,
`to_be_nil`/`to_be_none`, `to_be_greater_than`, etc. as BDD-matcher
intrinsics and handles them directly on the raw receiver value (bool, text,
array, ...) — **`to_be_true` and `to_be_false` were simply missing from
this list** (verified: neither string appears anywhere else in
`interpreter_method/*.rs` either). Since they're not intercepted, the call
falls through ~1100 lines later to the generic "look up a user-defined
class method on this value's runtime type" path, which sees
`type_name() == "bool"` (the raw value, not `ExpectHelper` — because
`expect()` never built one) and reports "method `to_be_true` not found on
type `bool`".

The pure-Simple `.spl` sources have **no mirror of this dispatch at all** —
`ExpectHelper` in `spec.spl` is the *intended* design (a real class with real
methods), but it is only reachable when running under a genuinely
self-hosted binary. Under the currently-deployed seed-derived binary, the
`expect(...).to_*()` chain never reaches `ExpectHelper` — it's fully
intercepted by the Rust intrinsic dispatcher, which is missing these two
names. There is nothing to fix in `.spl` for this specific gap; the fix must
land in the Rust seed.

## Fix Applied

`src/compiler_rust/compiler/src/interpreter_method/mod.rs`:
- Added `"to_be_true"` / `"to_be_false"` to the BDD-matcher-intrinsic guard
  list (alongside `to_be_truthy`/`to_be_falsy`, ~line 242-243).
- Added two new match arms (after the `to_be_falsy` arm, before
  `to_be_nil`/`to_be_none`) implementing them with **strict** boolean
  equality (`recv_val == Value::Bool(true)` / `Value::Bool(false)`), unlike
  `to_be_truthy`/`to_be_falsy` which accept any truthy/falsy value — this
  mirrors `ExpectHelper.to_be_true`/`to_be_false` in `spec.spl` exactly
  (`self.value != true` / `!= false` fails the assertion).

No changes to `to_equal`/`to_be_nil`/`to_be_truthy`/`to_contain` arms — no
regression expected there.

## Verification blocker (workspace instability, not this bug)

The workspace has heavy concurrent jj activity (parallel agent sessions
force-rebasing `main` and resolving unrelated conflicts, per
`.claude/rules/vcs.md`). During this investigation an initial version of
this same fix was silently clobbered by a concurrent working-copy
reconcile (matches the documented "Write Tool Silent Drops" / "Concurrent
checkout" pitfalls) — it had to be reapplied and committed immediately.
A `cargo build --release -p simple-driver --bin simple` attempt also failed
on an unrelated, pre-existing `simple-runtime` re-export error
(`rt_array_all`/`rt_array_any`/`rt_array_filter`/`rt_array_find`/
`rt_any_add` missing from `value` module exports) that another concurrent
session appears to be fixing in parallel (`fix(seed): bridge collections
rt_array_all/any/filter/find + rt_any_add re-exports` visible in `jj log`
at the time of writing). Rebuilding the seed and redeploying
`bin/release/<triple>/simple` to verify this fix end-to-end should be done
once the workspace settles (that unrelated build break resolves).

## Verification steps (once rebuilt/deployed)

```bash
cat > /tmp/tbt_spec.spl << 'EOF'
use std.spec
it("to_be_true works", fn(): expect(true).to_be_true())
it("to_be_false works", fn(): expect(false).to_be_false())
it("to_be_truthy works", fn(): expect(true).to_be_truthy())
it("to_be_nil works", fn(): expect(nil).to_be_nil())
EOF
timeout 120 bin/simple test /tmp/tbt_spec.spl
```

Before fix (current deployed binary): first two cases fail with
`semantic: method to_be_true/to_be_false not found on type bool`; the
latter two already pass (confirms no regression path — they hit a
different, unmodified match arm).
