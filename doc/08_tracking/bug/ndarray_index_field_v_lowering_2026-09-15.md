# ndarray specs fail with "class Index has no field named V" from src lowering (2026-09-15)

- Specs: `test/01_unit/lib/nogc_async_mut/ndarray_mean_axis_spec.spl`,
  `ndarray_empty_public_reductions_spec.spl`, `ndarray_generator_hardening_spec.spl`,
  `ndarray_view_bounds_spec.spl`.
- Observed: e.g. mean_axis `it "rejects zero-row axis mean"` fails with
  `semantic: class 'Index' has no field named 'V'` although the spec never references a
  field `V`, and no `.V` text exists in `src/lib/nogc_async_mut/ndarray/**` or
  `src/lib/common/science_math/ndarray.spl` (Index is defined there with field `value`).
  The error surfaces while executing `Shape.new`/`try_mean_axis` — i.e. from src-side
  generic/lowering machinery, not from the spec text.
- Unblock condition: find the lowering path that synthesizes/reads field `V` on `Index`
  (suspect generic monomorphization `Index<V>` or a stale SMF cache entry) and fix it in
  the compiler; the four specs should then pass unchanged.
