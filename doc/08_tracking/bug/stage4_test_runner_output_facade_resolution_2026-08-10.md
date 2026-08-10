# Stage 4 test output resolves incomplete `std.io` path facade

- **Date:** 2026-08-10
- **Component:** Stage 4 monomorphization / `std.test_runner.test_runner_output`
- **Severity:** P1 bootstrap blocker
- **Status:** fixed (2026-08-10)
- **Fix commit:** `4d72f950389`

## Symptom

After the `test_runner_execute` owner fix, the R15 resume recorded in
`stage4-resume-b55fb55.log` advanced to
`src/lib/nogc_sync_mut/test_runner/test_runner_output.spl` and failed to
resolve `path_basename` through the broad `std.io` facade.

The canonical implementation was present, but the strict Stage 4 closure did
not expose it reliably through that facade.

## Fix

Commit `4d72f950389` imports `path_basename` directly from
`std.nogc_sync_mut.io.sysinfo_ops`.  It also extracts `result_doc_name(path)`
as a pure helper used by document-style result formatting, giving the owner
binding a focused behavior surface that can be compiled and tested directly.

## Regression coverage

`test/01_unit/app/test_runner_output_owner_spec.spl` verifies:

- the exact concrete-owner source contract and absence of the former
  `std.io` import;
- the production doc-output call through `result_doc_name`;
- POSIX nested paths reduce to their basename;
- Windows path separators also reduce to the basename, preventing the same
  failure from being hidden by host-specific path behavior.

## Verification evidence

Fresh Stage 3 archive compilation passed for the repaired module and its
regression spec:

- module archive: `/tmp/simple-r15-output-owner.YySfZh/output.a`
- module build log: `/tmp/simple-r15-output-owner.YySfZh/build.log`
- regression-spec archive: `/tmp/simple-r15-output-spec.ip0JnF/spec.a`
- regression-spec build log: `/tmp/simple-r15-output-spec.ip0JnF/build.log`

These receipts establish that the concrete owner import, pure helper, and
cross-platform prevention spec compile through the fresh Stage 3 lane.  Full
Stage 4 convergence remains pending and is not claimed by this record.
