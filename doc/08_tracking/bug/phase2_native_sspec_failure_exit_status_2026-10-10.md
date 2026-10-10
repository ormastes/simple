# Native SSpec capsule returns zero with failed examples

Status: OPEN.

A native Phase2 capsule of `test/01_unit/compiler/mir/folded_global_scalar_helper_spec.spl` was constructed with stub fallback disabled. It compiled 406 modules with zero failures in 35 seconds. Executing it printed `3 examples, 2 failures`, while returning process exit zero. The ordinary immutable-read example passed; both address-storage examples failed. Exit zero therefore does not qualify this test execution.

Evidence: `build/native_probe/traceability-release-folded-spec-pass2/spec-run.log` and `spec-run-status.txt`. Fail closed on nonzero reported failure count; do not substitute process exit alone for SSpec outcomes. No test PASS or release admission is claimed. The third focused diagnostic attempt retains assertions and only adds diagnostic output, with a hard stop afterward.
