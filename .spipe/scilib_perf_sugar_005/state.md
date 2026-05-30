# Feature: scilib-perf-sugar-005

## Raw Request
fix all remain bug and feature request and abandon plans.. and in mind pure simple is main rust is just seed. use skill $sp_dev

Selected tracker: `doc/08_tracking/feature_request/scilib_perf_sugar.md`, `PERF-SUGAR-005`.

## Task Type
feature

## Refined Goal
Prove and record that NDArray slicing now uses stride-aware metadata views instead of copying data for row, column, and stepped slice access.

## Acceptance Criteria
- AC-1: 1-D slices expose `Layout.Strided`, updated offset, and updated stride metadata.
- AC-2: Stepped 1-D slices carry non-unit stride metadata and still resolve values correctly.
- AC-3: Row views are metadata-only and keep row-major element stride.
- AC-4: Column slices are metadata-only and carry non-contiguous row stride.
- AC-5: `PERF-SUGAR-005` is updated with verification evidence.
- AC-6: Focused tests include backing-array evidence that views are not selected-element copies, plus chained-view composition.

## Scope Exclusions
Compiler index sugar such as `A[i, ..]`, native pointer view types, and mutable aliasing semantics are out of scope for this closure; the existing NDArray API exposes `slice`, `slice_2d`, `row`, and `column`.

## Phase
dev-done

## Log
- dev: Added focused metadata assertions to `test/feature/scilib/ndarray_slice_spec.spl`.
- dev: Updated stale slice-spec prose from copy/v1.1 language to current stride-aware view behavior.
- dev: Added backing `data_f64.len()` invariants, negative-step slicing, chained 1-D view, non-origin 2-D view, and row/column-from-view coverage.
