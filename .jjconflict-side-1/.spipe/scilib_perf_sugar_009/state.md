# Feature: scilib-perf-sugar-009

## Raw Request
fix all remain bug and feature request and abandon plans.. and in mind pure simple is main rust is just seed. use skill $sp_dev

Selected tracker: `doc/08_tracking/feature_request/scilib_perf_sugar.md`, `PERF-SUGAR-009`.

## Task Type
feature

## Refined Goal
Expose existing NDArray Float64 scalar broadcast helpers through arithmetic operator sugar so `a + Float64.new(x)` and related operations no longer require explicit scalar method calls.

## Acceptance Criteria
- AC-1: `NDArray` supports `+`, `-`, `*`, and `/` with a `Float64` right-hand scalar in interpreter mode.
- AC-2: Operator sugar reuses existing `add_scalar`, `sub_scalar`, `mul_scalar`, and `div_scalar` implementations so SIMD/tail behavior stays centralized.
- AC-3: Focused scilib tests cover the operator sugar for add, sub, mul, and div.
- AC-4: `PERF-SUGAR-009` is updated with the implemented behavior and verification evidence.

## Scope Exclusions
Float32 operator sugar, reverse scalar-left operators, compiler lowering for math blocks, and native backend support are out of scope for this small observed-gap fix.

## Phase
dev-done

## Log
- dev: Added interpreter object-operator fallback from `+`, `-`, `*`, and `/` to `add_scalar`, `sub_scalar`, `mul_scalar`, and `div_scalar` when the left object exposes those methods.
- dev: Extended `test/feature/scilib/ndarray_broadcast_spec.spl` with arithmetic operator sugar coverage.
- dev: Fixed multi-dimensional `flat_*` accessors to compute offsets directly instead of making nested `self` method calls from helper functions.
