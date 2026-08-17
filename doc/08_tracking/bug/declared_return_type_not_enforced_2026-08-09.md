# BUG: declared function return types are not enforced by any engine

- **Filed:** 2026-08-09
- **Lane:** G4
- **Severity:** High (silent wrong values; hides entire defect classes)
- Status: OPEN (P1)
- Status re-verified 2026-08-17 by source inspection (triage shard 00).
- **Discovered via:** `dotq_tail_position_in_bool_returning_fns_2026-08-09.md`

## Symptom

A function may return a value of any type from a signature declaring any other
type. No error, no warning, no coercion — the foreign value is passed straight
through to the caller.

## Reproduction (2026-08-09, `bin/simple run`)

```
fn ret_text() -> bool:
    "not-a-bool"

fn tail_dotq(xs: [text]) -> bool:
    xs.?          # yields [text]? per spec, never a bool

fn main():
    print("ret_text => " + ret_text().to_text())
```

Rust seed / default JIT:

```
ret_text           => <special:129>
tail_dotq nonempty => true
tail_dotq empty    => true
EXIT=0
```

Interpreter (`SIMPLE_EXECUTION_MODE=interpreter`), same source:

```
error: semantic: method `to_text` not found on type `array` (receiver value: [x, y])
EXIT=1
```

Three facts:
1. `ret_text() -> bool` returning a `text` literal compiles and runs to
   completion with **exit 0**, yielding the garbage value `<special:129>`.
2. The interpreter propagates the raw `array` out of a `-> bool` function; the
   only diagnostic arrives incidentally, from a *downstream* method lookup, and
   names the wrong thing (`to_text` not found) rather than the return-type
   violation.
3. The two engines produce different values for the same `-> bool` function, so
   the missing check also masks an engine-divergence bug.

## Impact

This is the gate that would have caught all 42 sites in the companion `.?` bug
at authoring time, five of them in compiler error-reporting paths. More broadly,
every `-> T` signature in the codebase is currently documentation rather than a
contract, so no return-type-shaped defect can be caught statically.

## Why it is not fixed in this change

Turning on return-type checking is not a contained edit:

- It belongs in `src/compiler/35.semantics/` / `src/compiler/30.types/type_system/checker.spl`,
  and must agree with the implicit-return (tail-expression) rule, `return` in all
  branch positions, `->` on lambdas, trait/impl method signatures, and generics.
- It will fail-loud across a large existing corpus that has never been checked —
  42 known `-> bool` violations alone, plus whatever else exists. Landing it
  without first repairing the corpus turns the build red.
- Two engines must be made to agree first (see fact 3 above); enforcing a
  contract that the backends implement differently just relocates the bug.

## Recommended sequencing

1. Repair the 42 `.?` sites (companion doc).
2. Add the checker in **warning** mode; census the true violation count.
3. Repair the census, then promote to error.

Do not promote to error before step 2 reports a number.


## Re-measurement 2026-08-17 (P0-core silent-wrong lane) — REPRODUCED, and worse

Binary: `bin/release/x86_64-unknown-linux-gnu/simple`, 59,536,728 bytes, mtime
2026-08-16 22:59:37 UTC (Rust seed).

```
fn wrong_ret() -> i64:
    "notanint"

fn main():
    val v = wrong_ret()
    print v
```

| engine | output |
|---|---|
| `SIMPLE_EXECUTION_MODE=interpreter` | `notanint` |
| `SIMPLE_EXECUTION_MODE=jit`         | `2910620488929` |

Exit 0 on both; no diagnostic from any phase.

The doc records this as "declared return types are not enforced by any engine",
which is true but understates the consequence. Two things this measurement adds:

1. **The two engines do not merely both fail to check — they produce DIFFERENT
   wrong answers.** The interpreter keeps the string, so `v` is a `text` in an
   `i64` binding and downstream arithmetic will fail somewhere else entirely,
   far from the cause. The JIT keeps the raw slot and prints it as an integer.
2. **The JIT's number is a heap address, not a value.** `2910620488929` is
   `0x2A5_5B0F_8FE1`-scale — the tagged heap pointer to the string, printed as
   an `i64` because the binding said `i64`. So an unenforced return type does
   not just yield a wrong number; it **leaks a live heap pointer into integer
   arithmetic**, where it can be added, compared, indexed with, or written to a
   file. That is a materially different severity argument from "the type is not
   checked", and it belongs in the case for prioritising the fix that this doc's
   "Why it is not fixed in this change" section defers.

No fix attempted here. The doc's own assessment that the fix is neither small
nor contained is not disputed by this measurement.

## Re-reproduced 2026-08-17 (batch_00) — still live, and the divergence widened

Confirmed on the deployed seed (`bin/simple`, mtime 2026-08-16 22:59). Fixture:

```simple
fn ret_text() -> bool:
    "not-a-bool"

fn main():
    val v = ret_text()
    print("ret_text => " + v.to_text())
```

| engine | exit | output |
|---|---|---|
| jit (default)                       | 0 | `ret_text => true` |
| `SIMPLE_EXECUTION_MODE=interpreter` | 0 | `ret_text => not-a-bool` |

Two changes since the 2026-08-09 filing, both making this *worse*, not better:

1. The JIT value drifted from `<special:129>` to **`true`**. The original garbage
   value at least looked wrong on sight; `true` is a plausible bool and will not
   attract a second glance. The defect is unchanged — a `text` literal is still
   being returned from a `-> bool` signature with no check — but its symptom is
   now camouflaged.
2. The interpreter no longer errors on this shape. On 2026-08-09 it happened to
   fail downstream (`method to_text not found on type array`). Here it exits **0**
   and prints the raw text straight through a `-> bool` signature. Both engines
   now exit 0 with different answers, so the incidental diagnostic that used to
   catch this case is gone.

Not fixed here, for the reason the original filing gives: enforcement belongs in
`30.types/type_system/checker.spl` / `35.semantics` and will fail loud across an
unrepaired corpus (42 known `-> bool` violations alone). This entry records only
that the bug is **live and re-confirmed**, and that the "already fixed?" question
is settled in the negative.
