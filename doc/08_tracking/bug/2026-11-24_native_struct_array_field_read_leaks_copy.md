# Native: reading an array field off a struct copies the array and never frees it

- Id: native_struct_array_field_read_leaks_copy_2026-11-24
- Status: open
- Found: 2026-11-24, duplicate-check RSS work (work/dupchk-mem)
- Layer: native codegen / runtime (seed `native-build`, `SIMPLE_NATIVE_BUILD_RUST=1`)

## Repro

```simple
struct V:
    ids: [i64]

fn f_field(v: V, n: i64) -> i64:
    var acc = 0
    var i = 0
    while i < n:
        val a = v.ids          # 20-element array
        acc = acc + a[i % 20]
        i = i + 1
    acc
```

5,000,000 iterations: **1,094 MB peak RSS, 3.8 s**. The same loop indexing a
`[f64]` parameter directly: **5 MB, 0.5 s**. About 220 bytes leak per field
read, so the array is copied on every read and the copy is never released.

## Impact

Duplicate-check cosine scoring read `vector.ids`, `vector.weights`, and so on
per scored pair through a `FeatureVec`. Over 900k pairs this added more than
2 GB of native peak RSS. The workaround in `similarity.spl`
(`interned_cosine_matches`) keeps the corpus in flat arrays that are indexed
only from locals.

## Expected

A field read should borrow the array or share it through a refcount. If it
does copy, the copy must be freed when the local goes out of scope.
