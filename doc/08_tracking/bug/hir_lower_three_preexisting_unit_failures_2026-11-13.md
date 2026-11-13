# Three pre-existing `hir::lower` Rust unit test failures (2026-11-13)

Status: open. Severity: P2 (seed unit tests red; no product spec known to depend on them).

## Reproduction
At origin/release/1.0.0 (7b8c3e323a3), on Windows with `windows-llvm-23.1.1.shs`
activated and `CC=CXX=clang-cl`, using a private `CARGO_TARGET_DIR`:

    cargo test -p simple-compiler --lib hir::lower
    test result: FAILED. 426 passed; 3 failed

These fail on the untouched origin tree, so they are pre-existing. They are not
caused by the Option<Enum> match payload fix (work/option-enum-match-20261113).

## Failures
1. `hir::lower::stmt_lowering::optional_bool_binding_tests::result_optional_projection_and_explicit_patterns_still_lower`
   (stmt_lowering.rs:4626). Fails with `CannotInferFieldType { struct_name: "i64", field: "ok" }`
   on `if val item = value.ok.?` over `Result<i64, text>`. The `.ok` projection is
   resolved against the payload type `i64`, not against the Result.
2. `hir::lower::expr::calls::some_record_payload_tests::existing_some_function_payload_keeps_its_function_binding`
   (calls.rs:1278). Fails with `Some(function) lost its typed Option: Some(Any)`.
   The payload type of `Some(<fn>)` is erased to Any.
3. `hir::lower::tests::lenient_global_diag_tests::lenient_lowering_records_dropped_list_comprehension`
   (lenient_global_diag_tests.rs:288). Fails with `dropped comprehension must be recorded, got []`.
   Lenient lowering no longer records the diagnostic.

## Next step
Bisect each one separately on release/1.0.0. They are independent: one is
projection typing, one is Some payload typing, and one is lenient-diagnostic
bookkeeping.
