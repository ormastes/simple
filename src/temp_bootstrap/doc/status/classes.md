# Feature: Classes & Methods — Feature #10

- **Importance**: 4/5
- **Difficulty**: 4/5
- **Status**: COMPLETED (minimal evaluator support)

## What was added
- Class definitions are tracked and objects can be instantiated via `ClassName { field: value }`.
- Method calls on objects execute the class method with `self` bound to the instance; fields are readable from `self`.
- New test `runner_handles_class_methods` verifies calling a method to read a field.

## Files touched
- `src/compiler/src/lib.rs` — class registration, object creation, method dispatch.
- `src/driver/tests/runner_tests.rs` — class/method coverage.
