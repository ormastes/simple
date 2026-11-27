# Integral f64 renders as an integer in text interpolation (`1.0` -> `"1"`)

- **Date:** 2026-07-25
- **Area:** f64 -> text conversion used by `"{x}"` interpolation and therefore
  by `std.common.convert.f64_to_text` (`src/lib/common/convert.spl:124`, which
  is just `"{n}"`).
- **Severity:** medium — lossy/ambiguous rendering; a serialized `1.0` reads
  back as an integer, and float values become indistinguishable from ints in
  logs, `to_string()` output, and any text-format round trip.
- **Status:** RESOLVED (fixed by `8469c335ed8`; verified 2026-11-25 — see below).

## Resolution (2026-11-25)

Fixed by commit `8469c335ed8` ("fix(float): integral f64 renders as \"1.0\"
not \"1\"; stop 1e-300 collapsing to 0.0", 2026-07-26, ancestor of
release/1.0.0 HEAD): all three f64→text lanes now emit the shortest decimal
that round-trips, forcing `.0` onto integer-looking values.

Verified on Windows with the pinned Rust seed
(`SIMPLE_LIB=src bin/simple.exe run`, run mode):

- Probe: `print "a={a} b={b} c={c} d={d} e={e}"` for
  `1.0 / -3.0 / 2.25 / 0.0 / 1000000.0` →
  `a=1.0 b=-3.0 c=2.25 d=0.0 e=1000000.0`.
- Tensor probe importing `std.pure.tensor`:
  `tensor_from_data([1.0, 2.0, 3.0], [3]).to_string()` →
  `PureTensor(shape=[3], data=[1.0, 2.0, 3.0])`.

The two `pending("f64_integral_to_text_drops_fraction_2026-07-25")` blocks in
`src/lib/gc_async_mut/pure/test/tensor_spec.spl` ("String Representation") are
un-pended in the same change, restoring the original `contains("1.0")` /
`contains("2.0")` assertions.

Verification limit: `bin/simple.exe test` cannot run any spec at
release/1.0.0 HEAD on this host (the pinned seed rejects the
`@representation_boundary` decorator added by cfd89933699, including in the
test runner's own sources), so the tensor spec itself was not executed;
the assertions were verified equivalent-by-probe in run mode as above.

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
