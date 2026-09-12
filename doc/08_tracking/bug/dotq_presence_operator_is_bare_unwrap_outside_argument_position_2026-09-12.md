# `.?` is a presence predicate only in call-argument position; everywhere else it is a bare unwrap

- Status: OPEN (2026-09-12)
- Severity: HIGH — silent wrong value, and the non-optional return contract is not enforced on the present path
- Area: Rust seed — `.?` lowering / return-contract check
- Binary: `bin/release/aarch64-unknown-linux-gnu/simple`, sha256 `3d120a6f9ab5`
- Lane: `bin/simple test` (interpreter)

## What `.?` is supposed to be

A presence check yielding `bool`. The tree uses it that way in both roles:
as a spec assertion (`expect(parsed.?).to_equal(true)`) and as the whole body of
`-> bool` predicate methods (`fn has_dep(name) -> bool: self.find_dep(name).?`).

## What it actually does

It yields `bool` **only when it appears syntactically as an argument to a call**.
In every other position it evaluates to the Optional's payload on `Some` and to
`nil` on absence. Measured, one spec file, same run:

| # | expression | result |
|---|---|---|
| A | `expect(some_box().?).to_equal(true)` | PASS |
| B | `expect(some_box().?).to_equal(false)` | FAIL — so the matcher does discriminate |
| C | `expect(Box(v: 7)).to_equal(true)` | FAIL — a struct is not `true`, no truthiness coercion |
| D | `expect(none_box().?).to_equal(false)` | PASS |
| E | `expect(none_box().?).to_equal(true)` | FAIL |
| F | `val v = some_box().?` then `expect(v).to_equal(true)` | **FAIL** |
| G | `val v = some_box().?` then `expect(v).to_equal(Box(v: 7))` | **PASS** |
| H | `fn tail_bool() -> bool: some_box().?` then `expect(tail_bool()).to_equal(true)` | **FAIL** |
| I | `fn tail_bool() -> bool: some_box().?` then `expect(tail_bool()).to_equal(Box(v: 7))` | **PASS** |
| J | `val v = (some_box().?)` — parenthesised | payload, `Box(v: 7)` |

A vs F is the whole bug: the identical expression is a `bool` inside the call and
the payload one line later. C rules out the obvious alternative explanation (that
the matcher merely coerces truthiness). J rules out an end-of-line lexing theory —
parentheses do not restore the predicate — so the trigger really is call-argument
position.

H and I are the dangerous pair: a `-> bool` function whose body is `X.?` returns a
**struct**, and nothing rejects it. The return contract is only enforced on the
absent path, where the value is `nil`:

```
semantic: nil is forbidden by the non-optional return contract of 'authenticate'
```

That error — a *wrong credential* raising a semantic error instead of returning
`false` — is how this was found; see
`doc/08_tracking/bug/simpleos_server_credential_zeroization_gap_2026-08-14.md`.

## Why this hides so well

Every spec written as `expect(x.?).to_equal(true)` is in argument position, so it
passes — and would keep passing regardless of what `.?` means anywhere else. The
predicate methods below are only wrong on the paths specs rarely take (the absent
path errors; the present path returns a truthy payload that behaves correctly
under `if`). So the tree looks green.

## Blast radius — `-> bool` functions whose body is `X.?`

Each returns the payload on `Some` and raises the non-optional-return error on
absence. Each is a one-line fix (replace with `match ...: Some(_): true / nil: false`).
Not fixed here: out of this pass's shard scope.

- `src/lib/nogc_sync_mut/database/bug.spl:150` — `is_split_table_db()`
- `src/lib/nogc_async_mut/database/bug.spl:150` — `is_split_table_db()` (duplicate of the above)
- `src/lib/nogc_sync_mut/database/server/durability.spl:483` — `durable_file_loads(path)`
- `src/app/pkg/lock.spl:47` — `has_entry(name)`
- `src/app/pkg/manifest.spl:108` — `has_dep(name)`, an `or` of two `.?`
- `src/app/interpreter/lazy/lazy_val_fixed.spl:388` — `contains(key)`
- `src/compiler/60.mir_opt/mir_opt/pattern/rule_engine.spl:276` — `optimization_rule_provider_can_run(...)`, `not X.?`
- `src/compiler/70.backend/linker/lazy_instantiator.spl:121` — `can_instantiate(symbol)` — **fenced** under an active codex lane, hand to that owner

Already fixed (this pass): `CapabilityTable.authenticate`,
`src/lib/nogc_sync_mut/database/server/capability.spl`.

## Likely mis-attribution this explains

`doc/08_tracking/bug/target_arch_enum_enum_collision_option_2026-07-18.md` reports
`parse_target_arch(name).?` "evaluating to the raw unwrapped enum value" and
attributes it to a `TargetArch` enum-vs-enum collision in the flat global type
registry. That symptom is exactly this defect, and it does not need a collision to
occur. Both same-named `TargetArch` enums still exist in the tree today while the
spec passes, which is consistent with the collision never having been the cause.

## Not fixed here

The lowering is in the Rust seed, outside this pass's pure-Simple scope. Filed
with the discriminating matrix so the owner can go straight to the argument-position
special case.
