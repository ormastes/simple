# Parsed match callback closure conversion

Requirement: REQ-SSPEC-COMPILER. Bug: [mir_match_lambda_capture_scope_2026_10_17](../../../08_tracking/bug/mir_match_lambda_capture_scope_2026_10_17.md).

Authored manual; execution and docgen **TEST_BLOCKED**. Source: `test/02_integration/compiler/match_lambda_closure_conversion_spec.spl`.

Seven parsed-source scenarios require zero HIR/MIR errors. They distinguish noncapturing matches from actual environments and check runtime capture operations for arm-body state, guard-only state, arm-local shadowing, parsed Or normalization, nested matches, and outer scrutinees. Expected registered result after qualified execution: seven passes, no skips. This is currently an expectation, not an execution receipt.

The external native fixture `test/fixtures/compiler/native_match_lambda_capture.spl` must return 0 with `match-closure:13,8,-2,6,7,5,10,12`. It tests independent returned closures and a captured by-value snapshot after the outer variable changes. Follow the linked bug report for the compiler command and custody requirements. A successful compile or presence of runtime calls alone does not establish this value oracle.
