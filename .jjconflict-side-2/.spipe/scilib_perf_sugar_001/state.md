# Feature: scilib-perf-sugar-001

## Raw Request
fix all remain bug and feature request and abandon plans.. and in mind pure simple is main rust is just seed. use skill $sp_dev

Selected tracker: `doc/08_tracking/feature_request/scilib_perf_sugar.md`, `PERF-SUGAR-001`.

## Task Type
feature

## Refined Goal
Make `mat_zeros` and `mat_identity` allocate typed numeric buffers through the existing pure-Simple allocation facade instead of per-element push loops, with the Rust seed registering the required runtime externs.

## Acceptance Criteria
- AC-1: `rt_f64_array_alloc`, `rt_f32_array_alloc`, `rt_i64_array_alloc`, and `rt_i32_array_alloc` are registered in the seed runtime and return zero-filled typed arrays of the requested length.
- AC-2: `mat_zeros` and `mat_identity` use `alloc_f64` from the pure-Simple science math allocation facade instead of building `Float64` data with repeated `push(0.0)`.
- AC-3: Focused unit coverage proves typed numeric allocation lengths and zero-fill behavior for f64/f32/i64/i32.
- AC-4: Existing linalg tests for zeros and identity pass in interpreter mode.
- AC-5: The `PERF-SUGAR-001` tracker is updated with landed behavior and verification evidence.

## Scope Exclusions
PERF-SUGAR-002 and later scilib items are not part of this increment.

## Phase
dev-done

## Log
- dev: Created state file with 5 acceptance criteria (type: feature).
