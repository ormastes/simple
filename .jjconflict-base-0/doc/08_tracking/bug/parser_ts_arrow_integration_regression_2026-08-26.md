# Parser integration test reports stale TsArrowFunction diagnostic

During the full `simple-parser` LLVM coverage run, 302 library tests passed but
`parser/tests/control_flow.rs::ts_arrow_detection_rule_was_retired_when_the_arrow_lambda_landed`
failed: actual diagnostic `Some(TsArrowFunction)`, expected `None`.

This blocks using the full integration suite as the identifier-owner coverage
receipt. The isolated library denominator is branch-complete, but parser release
readiness remains open until the diagnostic rule or expectation is reconciled.

