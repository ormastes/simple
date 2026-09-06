# Integral f64 renders as an integer in text interpolation (`1.0` -> `"1"`)

- **Date:** 2026-07-25
- **Area:** f64 -> text conversion used by `"{x}"` interpolation and therefore
  by `std.common.convert.f64_to_text` (`src/lib/common/convert.spl:124`, which
  is just `"{n}"`).
- **Severity:** medium — lossy/ambiguous rendering; a serialized `1.0` reads
  back as an integer, and float values become indistinguishable from ints in
  logs, `to_string()` output, and any text-format round trip.
- **Status:** OPEN.

## Symptom

```
bin/simple test <probe spec>
```

probe body:

```
val a = 1.5
val b = 2.25
val c = -3.0
print "A={a} B={b} C={c}"
```

output:

```
A=1.5 B=2.25 C=-3
```

Non-integral values render correctly. Integral values silently lose the
fractional part: `1.0` -> `1`, `-3.0` -> `-3`.

## Expected

`1.0` should render as `1.0` and `-3.0` as `-3.0`, matching Rust's `{}` for
`f64` and Python's `repr(float)`. A float should always be recognisable as a
float in its default text form.

## Impact found in practice

`src/lib/gc_async_mut/pure/test/tensor_spec.spl` "String Representation" block
asserts `t.to_string().contains("1.0")` for a tensor holding `1.0`. The
assertion is correct and the tensor really does render every element; only the
f64 formatting is wrong. Those two examples are therefore left `pending` rather
than weakened to `contains("1")`, which would bake the defect into the suite.

## Note

`src/lib/common/convert.spl:124` `f64_to_text` delegates straight to `"{n}"`,
so fixing the interpolation path fixes the stdlib helper too. There is
currently no correct float formatter anywhere in `src/lib/common/`.
