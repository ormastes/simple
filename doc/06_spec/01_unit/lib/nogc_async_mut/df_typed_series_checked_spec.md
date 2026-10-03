# Checked typed column contract

Status: **authored companion; not generated or runtime verified** (2026-10-03).
Source: `test/01_unit/lib/nogc_async_mut/df_typed_series_checked_spec.spl`.
Requirement: REQ-001, partial CP-001-A/C. Eight scenarios use the production
typed-column, Series and NDArray APIs. No engine parity or numerical-join
acceptance is inferred.

The additive checked API exports `TypedColumnError`: `MaskLength(expected,
actual)`, `IndexOutOfBounds(index,length)`, `DTypeMismatch(expected,declared,
storage)`, and `InvalidStorage(reason)`. `from_masked_checked`, `validate`,
`get_checked` and numeric `_from_dynamic_checked`/`_into_dynamic_checked`
adapters expose these errors. Existing signatures and shared `DfError` remain
unchanged; legacy adapters/read/construction map checked failures to the
existing `ShapeMismatch`. Existing transform methods still use that legacy
error contract; callers may use `validate` for detailed mask information.

| Scenario | Fixture and oracle |
|---|---|
| Mask lengths | Two values with zero mask bits produce `MaskLength(2,0)`; legacy constructor still produces `ShapeMismatch` |
| Checked indices | Two rows reject -1 and 2 with exact index/length payload; index 0 is 7 and masked index 1 is a successful absent value |
| Dtype diagnostics | f64 storage requested as i64 reports both actual dtypes; forged outer i64 metadata still exposes f64 backing |
| Invalid storage | Negative dimension, shape/stride rank mismatch, overflowing element count, short backing, negative offset, positive/negative escaping stride and rank zero each reject before flat reads; legacy adapter also rejects |
| Valid views | Reversed stride -1/offset 2 reads 33,22,11; multidimensional 1x3 view retains 11 through 33 |
| Empty/mask | Empty 1D storage converts; a three-element dynamic column with one mask bit reports `MaskLength(3,1)` |
| Output/callback safety | Directly malformed typed column exposes mask error; checked and legacy conversion reject; real panic callback must never execute on rejected map |
| f64 roundtrip | Checked conversions preserve present -1.25 and 3.5 plus the middle missing row |

Storage validation precedes `Series.len`/flat access. It checks dtype first,
then shape/stride rank and nonnegative dimensions, overflow-safe element count,
offset and signed-stride reachable backing extents, then mask length. Bounds
use divisions before multiplication so malformed extents cannot wrap into a
plausible address. Empty dimensions cause zero reads. Valid multidimensional,
strided and reversed views remain supported.

`std.ndarray` logical-index helpers do not validate actual backing-array
extents; this boundary adds the missing validation before those accessors.
Sync and async variants share the same algorithm with variant-local Series
types. Mirrored test text is a contract, not evidence that either variant or
any backend has executed successfully.

Test-first commit precedes source implementation. No admitted runtime was run,
so RED/GREEN, compilation, generated manual admission and full REQ-001 remain
unproven. Numeric NaN/signed-zero joins, exact callback traces across engines,
planner lowering and NFR gates remain in the full acceptance plan.
