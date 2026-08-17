# BUG: `.?` existence check lowers to a raw scalar truthiness test on the JIT/native backend

> **CLAIMED-OFFHOST 2026-08-17** — do not work locally; assigned to a second host. See doc/03_plan/infra/priority_bug.md

- **Filed:** 2026-07-27
- **Lane:** NILQ
- **Severity:** High (silent wrong-branch; no diagnostic)
- Status: OPEN (P1)
- Status re-verified 2026-08-17 by source inspection (triage shard 01).
- **Engines affected:** JIT / native default engine only. The interpreter is correct.

## Specification

`doc/07_guide/quick_reference/syntax_quick_reference.md` L497-531 is unambiguous:

> The `.?` operator checks if a value is **present** (not nil AND not empty).
> It returns `T?` — the value itself if present, `nil` if absent.

with the per-type table:

```
opt.?    # T?:     pass-through (already optional)
list.?   # [T]?:   Some(list) if non-empty, nil if []
str.?    # text?:  Some(str) if non-empty, nil if ""
num.?    # i64?:   Some(num) — primitives always present
flag.?   # bool?:  Some(flag) — primitives always present
```

So: **`.?` is a PRESENCE test, never a zero-test and never a
pointer-non-null test.** `0.?` is present. `"".?` is absent.

## Actual behaviour — truth table

Bare-truthiness form `if x.?:`. Both columns produced by the same binary
(`bin/simple`, which currently prints the Rust bootstrap-seed banner); the
engine is selected with `SIMPLE_EXECUTION_MODE=interpreter`.
Repro: `build/nilq_probe/tt_dotq.spl`.

| receiver | spec expects | JIT (default) | interpreter |
|---|---|---|---|
| bare `i64` `0` | true | **false** :x: | true |
| bare `i64` `1` | true | true | true |
| bare `i64` `-1` | true | true | true |
| `Option<i64>` `Some(0)` | true | **false** :x: | true |
| `Option<i64>` `Some(5)` | true | true | true |
| `Option<i64>` `None` | false | false | false |
| `Option<text>` `Some("")` | false | **true** :x: | false |
| `Option<text>` `Some("x")` | true | true | true |
| `Option<text>` `None` | false | false | false |
| bare `text` `""` | false | **true** :x: | false |
| bare `text` `"x"` | true | true | true |
| `[i64]` `[]` | false | **true** :x: | false |
| `[i64]` `[1,2]` | true | true | true |

**JIT: 5 of 13 wrong. Interpreter: 13 of 13 correct.**

## The decisive evidence: the two engines return DIFFERENT TYPES

`build/nilq_probe/tt_value.spl` prints the *value* of `x.?` rather than only
its truthiness. This is the cleanest statement of the defect:

| expression | spec says | JIT returns | interpreter returns |
|---|---|---|---|
| `(0).?` | `Some(0)` → `0` | `false` (**bool**) | `0` (**i64?**) |
| `(7).?` | `Some(7)` → `7` | `true` (**bool**) | `7` (**i64?**) |
| `Some(0).?` | `0` | `false` | `0` |
| `Some(5).?` | `5` | `true` | `5` |
| `None.?` | `nil` | `false` | `nil` (`.to_text()` on it errors — genuinely nil) |
| `"".?` | `nil` | `true` | (nil) |
| `"xy".?` | `"xy"` | `true` | `"xy"` |
| `[].?` | `nil` | `true` | (nil) |
| `[1,2].?` | `[1,2]` | `true` | `[1,2]` |

**The JIT's `.?` returns a `bool` from a raw truthiness test. The
interpreter's `.?` returns `T?` exactly as specified.** Same operator, same
source, two different result *types*. The interpreter is right.

### This reconciles the two independent lane reports
- Lane TOINT saw "`.?` is false for a valid `Some(0)`, and on the interpreter
  it isn't even a bool" — that is the JIT column (bool, zero-test) and the
  interpreter column (`T?`) of the table above.
- Lane SPECFIX saw "`expect(xs.?).to_equal(true)` is a no-op because `.?`
  yields the receiver rather than a bool" — that is the interpreter column.

They are the same defect observed from opposite engines. Note the consequence
for the `expect(x.?).to_equal(true)` idiom, which differs per engine:
- on the **interpreter** it compares a `T?` against a bool → asserts nothing;
- on the **JIT** it does assert, but it asserts the *wrong* predicate —
  `x != 0` for integers, and a constant `true` for any `text`/array receiver
  (so it is vacuous there too).

Either way the idiom is not a presence assertion. See the companion
containment bug for the 1,954 affected assertion sites.

## Root cause (inferred from the shape of the failures)

The JIT/native lowering of `.?` emits a **raw machine-word `!= 0` test on the
representation** instead of a presence test:

- for an `i64` payload the word IS the integer, so the test degenerates to
  `x != 0` — a **zero-test**, wrong for `0` / `Some(0)`;
- for `text` / array the word is a heap pointer which is never null, so the
  test is **constant true** — the emptiness half of the spec is dropped
  entirely, wrong for `""` / `[]`.

Both error directions are explained by that single mis-lowering. The
interpreter evaluator implements the spec correctly, which is why the two
engines disagree on exactly the 5 rows above.

**Where the fix belongs:** the JIT/native lowering of the existence-check
operator in the compiler tree (`src/compiler/**`). **Not patched here** —
several lanes are live in that tree. The interpreter path needs no change; it
is the correctness oracle for this operator.

## What is NOT affected (important — limits the blast radius)

- **`if val x = opt.?:` pattern binding is CORRECT on BOTH engines**, including
  `Some(0)` (binds, `x == 0`) and `None` (does not bind).
  Repro: `build/nilq_probe/tt_bind.spl`. Only the *bare-truthiness* form is
  broken. The dominant real-world idiom is therefore safe.
- **`== nil` / `!= nil` is correct and mutually consistent on BOTH engines**,
  15/15 rows including `Option<struct>`. Repro: `build/nilq_probe/tt_cmp.spl`.
  This is the recommended containment idiom.

## Secondary divergence (spec-ambiguous, still a defect)

`Option<text>` holding `Some("")`:

- bare `if opt.?:` — JIT true, interpreter false.
- `if val x = opt.?:` — JIT **binds** `""`, interpreter **does not bind**.

The spec says `opt.?` is "pass-through (already optional)" (implying present)
but also that text is present iff non-empty. The two engines picked opposite
readings. The spec must be tightened *and* the engines made to agree.

## Minimal repros

- `build/nilq_probe/tt_dotq.spl` — the truth table above.
- `build/nilq_probe/tt_cmp.spl` — `== nil` / `!= nil` control (all green).
- `build/nilq_probe/tt_bind.spl` — `if val` binding control (green except the
  empty-text divergence).

## Containment landed by lane NILQ

See `doc/08_tracking/bug/dotq_zero_test_hazard_call_sites_2026-07-27.md`.
