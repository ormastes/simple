# Build Intermediate Lifecycle Implementation Report

## Result

Implemented fail-safe native-build intermediate management without changing incremental cache ownership or requested output semantics.

## Behavior

- Scans only the resolved output parent once at build start.
- Deletes only matching `.simple-native-build-...tmp` siblings older than 24 hours.
- Deletes failed-build staging output by default.
- Deletes successful bootstrap LLVM scratch by default.
- Retains current diagnostic scratch with `--keep-intermediates` or `SIMPLE_KEEP_BUILD_INTERMEDIATES=1`.
- Retains and prints exact paths with `--print-intermediates` or `SIMPLE_PRINT_BUILD_INTERMEDIATES=1`.
- Preserves incremental objects, receipts, final artifacts, and explicitly requested SMF/object/archive/shared outputs.

## Evidence

- `build_intermediate_policy_spec.spl`: 3/3 PASS.
- `build_intermediate_lifecycle_spec.spl`: 1/1 PASS.
- `bootstrap_llvm_success_cleanup_spec.spl`: focused policy regression PASS.
- Direct environment runtime guard: PASS.
- `doc/06_spec` executable-spec placement count: 0.
- File-level `simple check` could not produce a valid verdict because the admitted runtime's lint and format subprocesses both returned `-1`; no check PASS is claimed.
