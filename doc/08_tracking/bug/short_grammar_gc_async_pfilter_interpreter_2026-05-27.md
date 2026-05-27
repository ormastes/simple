# Short Grammar Placeholder Fails For gc_async_immut pfilter In Interpreter

Date: 2026-05-27
Status: open

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

In `test/unit/lib/gc_async_immut/native_combinators_spec.spl`, changing only
the `pfilter` callback to `_1 % 2 == 0` makes the interpreter run report
`total_passed: 0` and `total_failed: 1`.

The native run accepts the placeholder form, and the same file accepts
`pmap([1, 2, 3], _1 * 3)` in interpreter mode. The mismatch appears specific
to `pfilter` placeholder predicates in interpreter execution.

## Impact

Keep `pfilter` predicates explicit in interpreter-covered GC async immutable
facade tests until the interpreter path supports this placeholder form.

