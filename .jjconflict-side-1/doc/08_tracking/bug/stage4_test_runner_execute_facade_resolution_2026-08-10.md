# Stage 4 test execution resolves incomplete `std.io` facade

- **Date:** 2026-08-10
- **Component:** Stage 4 monomorphization / `std.test_runner.test_runner_execute`
- **Severity:** P1 bootstrap blocker
- **Status:** fixed (2026-08-10)
- **Fix commit:** `b55fb55a215`

## Symptom

The R15 resume recorded in `stage4-resume-7b70d51.log` passed the repaired
`test_runner_files` and `test_manifest_scanner` modules, then failed while
monomorphizing `src/lib/nogc_sync_mut/test_runner/test_runner_execute.spl`.

The strict Stage 4 closure could not resolve these functions through the
broad `std.io` facade:

- `time_now_unix_micros`
- `process_run_bounded`
- `process_run_with_limits_bounded`
- `file_size_raw`
- `file_modified_time`

## Fix

Commit `b55fb55a215` imports each helper from its concrete owner:

- file metadata from `std.nogc_sync_mut.io.file_ops`
- time from `std.nogc_sync_mut.io.time_ops`
- bounded processes and `ProcessResult` from
  `std.nogc_sync_mut.io.process_ops`

## Regression coverage

`test/01_unit/app/test_runner_bounded_output_contract_spec.spl` now provides:

- an exact source contract that requires the concrete owner imports and
  rejects the former `std.io` imports;
- bounded-process checks for stdout, stderr, exit status, and limit state;
- a monotonic behavior check for the imported microsecond clock;
- adjacent file-size and modification-time checks, including deleted-file
  behavior to prevent the metadata imports from regressing independently.

## Verification evidence

Fresh Stage 3 archive compilation passed for both the repaired module and the
final regression spec:

- module archive: `/tmp/simple-r15-execute-owner.sisAoP/execute.a`
- module build log: `/tmp/simple-r15-execute-owner.sisAoP/build.log`
- regression-spec archive: `/tmp/simple-r15-execute-spec-final.roWBUc/spec.a`
- regression-spec build log: `/tmp/simple-r15-execute-spec-final.roWBUc/build.log`

These receipts establish that the concrete owner imports and regression
coverage compile through the fresh Stage 3 lane.  Full Stage 4 convergence
remains pending and is not claimed by this record.
