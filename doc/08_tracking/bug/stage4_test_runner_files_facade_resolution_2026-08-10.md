# Stage 4 test-runner file discovery resolves incomplete `std.io` facade

- **Date:** 2026-08-10
- **Component:** Stage 4 monomorphization / `std.test_runner.test_runner_files`
- **Severity:** P1 bootstrap blocker
- **Status:** fixed (2026-08-10)
- **Fix commit:** `84581f8d417fed5650b458910b8ef447e57529cf`

## Symptom

R15 at `ff9ec1c6aaa` reached Stage 4 monomorphization and then failed to
resolve `path_basename` and `dir_walk` from `std.io` while compiling
`src/lib/nogc_sync_mut/test_runner/test_runner_files.spl`.

The module imported those functions through the broad `std.io` facade.  That
facade did not provide a reliable owner surface in the strict Stage 4 closure,
so both symbols remained unresolved even though their canonical modules were
present.

## Fix

Commit `84581f8d417` binds discovery directly to the canonical owners:

- `path_basename` from `std.nogc_sync_mut.io.sysinfo_ops`
- `dir_walk` from `std.nogc_sync_mut.io.dir_ops`

The existing `file_read` and `file_exists` imports remain on `std.io`; they
were not implicated by the failure.

## Regression coverage

`test/01_unit/app/test_runner_strip_ansi_spec.spl` now exercises both affected
surfaces through `test_runner_files`:

- basename classification for normal, hidden, and `.skip` files;
- real temporary-directory discovery through `discover_test_files_slow`.

## Verification evidence

Fresh Stage 3 archive builds passed after the fix:

- module archive: `/tmp/simple-r15-test-runner-owner-stage3.kA6tDy/test_runner_files_owner.a`
- module build log: `/tmp/simple-r15-test-runner-owner-stage3.kA6tDy/build.log`
- regression-spec archive: `/tmp/simple-r15-test-runner-spec.9INQfp/spec.a`
- regression-spec build log: `/tmp/simple-r15-test-runner-spec.9INQfp/build.log`

These receipts prove the corrected owner imports and regression spec compile
through the fresh Stage 3 lane.  Full R15 convergence remains a separate
bootstrap gate and is not claimed by this bug record.
