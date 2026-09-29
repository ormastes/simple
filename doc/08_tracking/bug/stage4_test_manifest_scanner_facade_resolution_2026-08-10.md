# Stage 4 test-manifest scanner resolves incomplete `std.io` facade

- **Date:** 2026-08-10
- **Component:** Stage 4 monomorphization / `std.test_runner.test_manifest_scanner`
- **Severity:** P1 bootstrap blocker
- **Status:** fixed (2026-08-10)
- **Fix commit:** `7b70d51e0cf`

## Symptom

The R15 Stage 4 resume at `84581f8d417` passed the previously repaired
`test_runner_files` module, then failed while monomorphizing
`src/lib/nogc_sync_mut/test_runner/test_manifest_scanner.spl`.

`dir_walk_native` and `path_basename` were imported through the broad
`std.io` facade.  The strict Stage 4 closure could not resolve those symbols
through that facade even though their canonical owner modules were present.

## Fix

Commit `7b70d51e0cf` binds both functions directly to their canonical owners:

- `dir_walk_native` from `std.nogc_sync_mut.io.dir_ops`
- `path_basename` from `std.nogc_sync_mut.io.sysinfo_ops`

## Regression coverage

`test/01_unit/app/test_runner_new/test_manifest_spec.spl` now creates a real
temporary directory and spec file, runs `manifest_full_scan`, and verifies
that the resulting manifest contains the discovered file with its full path.
This exercises both corrected owner imports through the production scanner.

## Verification evidence

Fresh Stage 3 archive compilation passed for the repaired module and its
regression spec:

- module archive: `/tmp/simple-r15-manifest-owner.Dfe8bC/scanner.a`
- module build log: `/tmp/simple-r15-manifest-owner.Dfe8bC/build.log`
- regression-spec archive: `/tmp/simple-r15-manifest-spec.dy6oFT/spec.a`
- regression-spec build log: `/tmp/simple-r15-manifest-spec.dy6oFT/build.log`

These receipts establish that the canonical imports and regression coverage
compile through the fresh Stage 3 lane.  Full Stage 4 convergence remains
pending and is not claimed by this record.
