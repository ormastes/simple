# Parser integration test reports stale TsArrowFunction diagnostic
**Status:** OPEN (unverified 2026-09-12)

During the full `simple-parser` LLVM coverage run, 302 library tests passed but
`parser/tests/control_flow.rs::ts_arrow_detection_rule_was_retired_when_the_arrow_lambda_landed`
failed: actual diagnostic `Some(TsArrowFunction)`, expected `None`.

This blocks using the full integration suite as the identifier-owner coverage
receipt. The isolated library denominator is branch-complete, but parser release
readiness remains open until the diagnostic rule or expectation is reconciled.


## Triage 2026-09-12
Rule D: record postdates 2026-07-29 and carries no short (<=3 min) repro; left open with a status line added since none existed. Binary identity (not run, no repro to verify): /home/yoon/dev/simple/bin/release/aarch64-unknown-linux-gnu/simple, 50,093,192 B, 2026-09-06 09:59.
