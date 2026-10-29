# Runner capture limit lacks native public visibility

Status: source repair prepared; native verification pending.

Attempt9 target source `c4708c981c51fb680a45da44f55efe1d400d3f32`,
compiled by admitted phase2 SHA-256
`c903ca1b0361d436829f9252cd3b7bafa0aba472d4c98a0bcd7e2943d374505e`,
failed nine runner module codegen operations. The retained log is
`/tmp/simple-release-1.0.0-phase2-runner-attempt9-20261030/stage2-test-runner-build-toolpin/cache/diagnostics/native-build-stderr-925714-2.log`.
It contains exactly nine identical diagnostics:

```text
[cranelift] imported non-public module static 'lib_nogc_sync_mut_test_runner_test_runner_types__TEST_OUTPUT_CAPTURE_BYTES' requires visibility-preserving accessor support
```

Affected modules: `test_executor_composite`, `test_runner_async`,
`gpu_lane_common`, `runner_lifecycle`, `app.test_runner_new.test_runner_main`,
`doctest_runner`, `native_owned_process`, `sdoctest.runner`, and `process_tracker`.
Each imports the constant directly from `test_runner_types`. The package already
exports this shared policy, but the definition was a private `val` without an
explicit export. Cranelift correctly refuses an external non-public static.

Repair: declare the existing constant `pub val` and explicitly export it from
its defining module. Keep its value and every consumer unchanged. The explicit
export also follows the strict export contract documented in
`doc/07_guide/language/module_system.md`. Do not relax backend private-static
protection: private accessors are not needed for this intentionally public API.

The native fixture
`test/fixtures/compiler/native_runner_capture_limit_visibility.spl` imports the
real provider and returns failure unless its runtime value is 4194304. Native
compile plus execution and the subsequent complete runner build remain required;
fixture authorship alone is not PASS. The independent missing backend diagnostic
message-file defect is outside this repair.
