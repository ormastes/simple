## Closed 2026-09-13 — already fixed, verified by running (MEASURED)

Does not reproduce. Ran a minimal receiver-enumeration repro against
`src/lib/nogc_async_mut/src/set.spl` on Windows x86_64 with the Rust seed
`bin/simple.exe` (`Simple Language v1.0.0-rc.1`, self-identified bootstrap seed):

```
union contains 1: true
union contains 4: true
inter contains 2: true
inter contains 1: false
```

Both `union` and `intersection` see a populated receiver and produce correct
results, which is exactly the behaviour the entry says was broken. The in-body
`Status: resolved` (top-level `items: [T]` index used for Set-to-Set operations
instead of traversing nested `Map` bucket arrays) is confirmed live. Closing.

Not covered by this run: the full `set_api_parity_spec.spl` suite did not
complete on this host — the test runner aborted at its own bound rather than
executing the spec, an unrelated runner-boundary issue on Windows. The direct
`bin/simple.exe run` repro above is the evidence.

---

# Generic Set binary operations see empty receiver

Date: 2026-05-14

## Summary

Pure Simple generic `Set<T>` methods that take another `Set<T>` can observe an
empty receiver when enumerating `self.to_list()` inside the method, even though
the same set enumerates correctly outside the method.

Status: resolved for the pure Simple `Set<T>` library by keeping a top-level
`items: [T]` index and using it for Set-to-Set operations instead of traversing
the nested `Map` bucket arrays during binary methods.

## Repro

Add the following case to
`test/01_unit/lib/nogc_async_mut/src/set_api_parity_spec.spl`:

```spl
it "supports union alias":
    val left = Set.from_array([1, 2, 3])
    val right = Set.from_array([2, 4])
    val union_set = left.union(right)
    expect(union_set.contains(1)).to_equal(true)
    expect(union_set.contains(4)).to_equal(true)
```

Run:

```sh
SIMPLE_LIB=src src/compiler_rust/target/debug/simple test test/01_unit/lib/nogc_async_mut/src/set_api_parity_spec.spl --mode=interpreter
```

Observed result before reverting the failing spec slice:

```text
expected false to equal true
```

Changing the implementation to cache `self.to_list()` and size the result from
that list produced `semantic: modulo by zero`, which indicates the receiver list
was empty inside the binary set operation.

## Impact

This blocks claiming Rust Simple API parity for generic pure Simple set
operations:

- `union`
- `intersection`
- `difference`
- `symmetric_difference`
- negative subset/superset cases should also be verified after the receiver
  issue is fixed.

## Current Passing Coverage

`test/01_unit/lib/nogc_async_mut/src/set_api_parity_spec.spl` currently covers the
passing baseline for:

- `Set.from_array`
- `size`
- `contains`
- `has`
- `add`
- `to_list`
- `to_array`
- positive `is_subset`
- positive `is_superset`

## Next Step

The failing set-operation assertions have been restored in
`test/01_unit/lib/nogc_async_mut/src/set_api_parity_spec.spl`. Keep this document as
evidence of the interpreter/lowering shape that motivated the library-level
workaround: nested `Map.keys()` returned an empty list inside Set-to-Set methods
while the top-level Set size remained correct.
