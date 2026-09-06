# Bug: `for x in <custom struct>` silently iterates zero times (no iterator protocol)

- **ID:** for_in_custom_struct_no_iterator_protocol_2026-06-15
- **Filed:** 2026-06-15
- **Severity:** P2 (language capability gap; silent wrong result)
- **Area:** interpreter / for-in loop / custom-type iterator protocol
- **Found by:** bytes-foundation feature (Phase-0 custom-type barrier)

## Summary

A `for x in span:` loop over a user-defined `struct` (here `ByteSpan`, a
behavior-carrying byte view) compiles and runs but iterates **zero times** —
the loop body never executes and the accumulator keeps its initial value. There
is no error, no diagnostic, and no fallback: it just silently does nothing.

This forces every custom collection type to expose `.to_bytes()` (materialize a
real `[u8]`) or an index loop with `.get(i)` for callers to iterate — defeating
the point of a zero-copy view and contradicting the Phase-0 plan's required
"iteration" behavior for `ByteSpan` (AC-2).

## Reproduction

```simple
use std.spec
use lib.common.bytes.span.{ByteSpan}
describe "iter probe":
    it "for-in over span sums to 60":
        val s = ByteSpan.new([10u8, 20u8, 30u8])
        var total = 0
        for byte_v in s:          # <-- never enters the loop body
            total = total + byte_v.to_i64()
        expect(total).to_equal(60)   # FAILS: total stays 0
```

Result: `Passed: 0 / Failed: 1` (the assertion sees `total == 0`).

## Works (current workaround)

```simple
for byte_v in s.to_bytes():        # iterating a real [u8] works -> 60
    total = total + byte_v.to_i64()
```

An internal index loop (`while i < len: ... get(i)`) also works. The
foundation ships a `ByteSpan.sum()` method that demonstrates internal iteration,
and tests use `for b in span.to_bytes()` for external iteration.

## Expected

Either:
1. `for x in obj` should resolve an iterator protocol method on the struct
   (e.g. a `next()`/`iter()` trait or an `__iter__`-style hook), OR
2. it should be a **compile error** ("type `ByteSpan` is not iterable") rather
   than silently iterating zero times.

Silent zero-iteration is the worst outcome: it produces wrong results that pass
type-checking and only surface via a value assertion.

## Notes

- `==` value-equality on a custom struct DOES work (structural compare) — only
  the for-in iterator protocol is missing.
- Distinct from `dict_struct_key_iteration_single_entry_2026-06-13` (dict keys)
  and `native_array_iteration_indexing_async_driver_smoke_2026-05-13` (array
  iteration under native driver); this is about user structs having no iterator
  hook at all.

## Re-measured 2026-09-06 — the SILENT half is gone, the feature gap remains

Host: `bin/release/aarch64-unknown-linux-gnu/simple`, 50093192 bytes,
mtime 2026-09-06 09:59 (aarch64 Linux), `SIMPLE_EXECUTION_MODE=interpret`.

Fixture (`build/wi/r_forin.spl`):

```simple
struct Bag:
    items: [i64]

fn main() -> void:
    val b = Bag(items: [1, 2, 3])
    var n = 0
    for x in b:
        n = n + 1
    print("for-in custom struct iterations={n}")
```

Observed:

```
error: semantic: cannot iterate over this type: Object { class: "Bag", fields: {"items": Array([Int(1), Int(2), Int(3)])} }
```

The record's headline symptom — "iterates zero times **with no error or
diagnostic**" — no longer holds: the loop now fails loudly and names the type.
The dangerous, silent-wrong-answer half of this row is therefore closed.

What is NOT closed, and this row should stay open for it: there is still **no
iterator protocol**. A user type cannot opt in to `for x in <my type>` at all.
That is a language capability gap, not a defect in the interpreter's loop
evaluator, and closing it means designing the protocol (a trait with a
`next()`/`iter()` contract, plus lowering in every engine), which is squarely
out of scope for an interpreter bug-fix pass and must not be faked by making
`for` guess at a struct's first array field.

Recommended re-triage: downgrade from "silent wrong result" to a feature
request for the iterator protocol, and re-file under language/type_system
rather than interpreter.

Scope: the **Rust seed's** interpreter lane. The pure-Simple interpreter
(`eval_stmts.spl`, the file the work package attributed this row to) was not
separately measured.
