## Closed 2026-09-13 — prior in-body resolution, carried forward (NOT re-verified this pass)

Reviewed in the 2026-05-and-earlier bug/todo tracking sweep. This entry already
recorded its own resolution before this pass; the header exists so the closure is
visible at the top rather than buried in the body. First status line found:

> Status: FIXED 2026-08-22 — Rust postfix parser preserves the callback boundary

This is a closure marker, not a new claim: the repro was **not** re-run in this
sweep. The original evidence in the body stands on its own. Re-open with a fresh
dated repro if the symptom returns — do not treat this header as verification.

---

# Short Grammar Placeholder Fails For gc_async_immut pfilter In Interpreter

Date: 2026-05-27
Status: FIXED 2026-08-22 — Rust postfix parser preserves the callback boundary

## Summary

`pfilter` from the `std.gc_async_immut` facade accepts an explicit predicate
lambda in interpreter mode:

```spl
pfilter([1, 2, 3, 4], \x: x % 2 == 0)
```

The equivalent placeholder predicate fails in interpreter mode:

```spl
pfilter([1, 2, 3, 4], _1 % 2 == 0)
```

## Evidence

The current exact reproducer is
`test/01_unit/lib/nogc_sync_immut/native_combinators_spec.spl`; the adjacent
named/explicit/placeholder comparison is
`test/01_unit/lib/nogc_async_immut/combinator_return_contract_spec.spl`.

The failure was reproduced again with the frozen Rust bootstrap seed on
2026-08-22. Named and explicit-lambda predicates passed. The actual trigger was
nesting the free-function combinator inside another call: `call_arg_depth`
deferred the unrecognized `pfilter` argument, then the outer transform promoted
the complete combinator call into a lambda.

## Impact

The Rust postfix parser's higher-order classifier now includes the immutable
`p*` combinator family. Placeholder grammar remains covered in the facade test;
no explicit-lambda normalization was needed.
