# BUG: declared function return types are not enforced by any engine

- **Filed:** 2026-08-09
- **Lane:** G4
- **Severity:** High (silent wrong values; hides entire defect classes)
- **Status:** Open — NOT fixed here. The fix is not small or contained; see below.
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
