# Generic Map<K,V> methods fail semantic lookup on dict receivers

Date: 2026-09-16
Status: OPEN

## Observed

`map_insert_if_absent_spec.spl`, `collections/src_collections_facade_spec.spl`
and `src/collections/src_collections_facade_spec.spl` fail with errors like:

```
semantic: method 'insert_if_absent' not found on type dict (receiver value: {})
```

Plain `map.len()` / `map.insert(k, v)` work; generic-typed helpers such as
`insert_if_absent` and some `get`-typed paths fail method resolution on
dict-typed receivers, and a raw `get` returns the unboxed/raw value.

## Impact

The collections facade specs cannot run; generic map helper APIs are unusable
on dict receivers in the interpreter.

## Expectation

`map.insert_if_absent(k, v)` (and the other generic Map helpers) resolve and
run for dict receivers, returning properly typed values.

## Unblock condition

Fix generic-method resolution on erased dict receivers (seed semantic layer).
Re-run the three specs listed above.
