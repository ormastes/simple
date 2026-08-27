# Rust-seed focused compiler-test RSS debt

Status: TODO

## Evidence

- Host: `x86_64-unknown-linux-gnu`
- Command: `cargo test -p simple-compiler erased_imported_class_method_does_not_guess_colliding_trait_vtable -- --nocapture`
- Result: PASS (`1 passed`, `0 failed`, `3678 filtered out`)
- Cold elapsed time: `6:04.05`
- Maximum RSS: `4,190,140 KiB`
- CPU: `654%`

The dispatch change adds only linear per-function nominal-hint collection and
removes an unknown-receiver scan across all trait method tables. The observed
RSS belongs to the monolithic Rust-seed compiler test build and is not evidence
of generated-program or dispatch hot-path memory growth, but it is too high for
a focused regression workflow and must remain visible as compiler-test
performance debt.

## Follow-up acceptance

- Measure cold and warm `--lib` filtered-test builds separately from full
  package test-target discovery.
- Attribute peak RSS between rustc compilation, linking, and test execution.
- Provide a focused compiler regression entrypoint whose cold peak RSS is below
  `2 GiB`, or document a measured host/toolchain lower bound and an approved
  ceiling.
- Preserve the erased-concrete/static and trait-typed/virtual assertions while
  reducing build scope; do not replace them with a parser-only or HIR-only test.
