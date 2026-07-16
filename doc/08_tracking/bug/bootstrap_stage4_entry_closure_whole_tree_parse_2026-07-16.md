# Stage 4 entry closure parses whole source trees before pruning

**Status:** SOURCE FIXED / RUNTIME VERIFICATION BLOCKED  
**Severity:** P0 bootstrap performance blocker  
**Observed:** 2026-07-16

## Symptom

The verified Stage-3 bootstrap compiler entered phase 2 with `n_sources=10503`.
After 180 seconds it was still parsing the initial compiler files at roughly
40 files per 100 seconds; no native-cache object was written. A 900-second
bounded run likewise timed out before backend work.

## Root cause

`run_native_build_bootstrap` pre-enabled
`SIMPLE_NATIVE_BUILD_ENTRY_CLOSURE=1` but called
`aot_native_project_with_backend_fixed` with four complete source roots. The
driver therefore collected every file before parsing, while its import-closure
walk only ran when closure mode was initially disabled.

## Source fix

- Stage 4 now seeds only `src/app/cli/main.spl` and starts closure mode at `0`.
- `CompilerDriver.load_sources_impl` now resolves a project entry's transitive
  imports before enabling closure mode, reusing the existing driver resolver.
- Source-contract tests reject the former four-root Stage-4 call.

## Verification blocker

The final bounded bootstrap invocation stopped before compilation because the
compiler-backfill archive is stale; the guard requires `--full-bootstrap`.
The mandatory three-cycle session cap is exhausted, so no fourth build was
started. The next fresh session must run one bounded `--full-bootstrap` cycle
and require phase 1 to report the reachable closure rather than 10,503 files.
