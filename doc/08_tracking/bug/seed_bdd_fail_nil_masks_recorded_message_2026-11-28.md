# Seed BDD `fail()` message masked by non-optional nil-return contract

Status: verification-pending
Date: 2026-11-28
Lane: ft29-1

## Symptom
A helper declared `-> T` whose body is `fail("unimplemented oracle")` (for
example `freeze_compile_snapshot` in
`test/03_system/app/compiler/feature/compiler_semantic_cache_manager_spec.spl`)
reported only `nil is forbidden by the non-optional return contract of
'freeze_compile_snapshot'`. The recorded failure message was lost.

## Cause
The seed's BDD builtin `fail()` (`interpreter_call/bdd.rs`) records the
assertion failure (`BDD_EXPECT_FAILED` + `BDD_FAILURE_MSG`) and evaluates to
`Value::Nil`. The `-> T` return then trips `validate_sffi_return_contract`
(`interpreter_call/core/function_exec.rs`), and the `it` block's Err path
printed only that contract error.

## Fix
In the `it` Err path, `err_report_message` substitutes the recorded BDD failure
summary when (a) a hard failure is recorded and (b) the error is the
nil-return-contract error. Unrelated errors are never replaced.

## Tests
Rust unit tests `fail_nil_mask_tests` in `bdd.rs`: reproduction (recorded
message wins), prevention (no recorded failure keeps the contract error;
unrelated errors are never replaced).

## Triage of related specs
- `compiler_semantic_cache_manager_spec.spl`: deliberately RED placeholder;
  assertions untouched; now reports "unimplemented oracle".
- `test/03_system/app/bootstrap/feature/windows_full_bootstrap_toolchain_suite_spec.spl`:
  all helpers are `fail("UNIMPLEMENTED: ...")` placeholders (same masking); left as is.
