# Bug: `for x in <custom struct>` silently iterates zero times (no iterator protocol)

Status: OPEN (P2)
Status re-verified 2026-08-17 by source inspection (triage shard 01).

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

## PARTIAL — re-verified 2026-08-17 (P2 triage, compiler lane)

The SILENT half is fixed: `src/compiler/10.frontend/core/interpreter/eval_stmts.spl:538`
now raises `eval_set_error("cannot iterate over " + val_kind_name(...))` as the
fall-through for a non-array/non-string receiver, so `for x in <custom struct>`
is a diagnostic rather than zero silent iterations.

The PROTOCOL half is not: `src/compiler/10.frontend/core/interpreter/value.spl:268-275`
`val_iterable_array` accepts only arrays and a struct literally NAMED `"List"`
(unwrapping its `items` field). No `next`/`iter` method lookup exists anywhere in
the interpreter directory, so a user-defined iterable is still not iterable.
Retitle scope to the protocol gap. NOT FIXED by this lane (P1-owned path).
