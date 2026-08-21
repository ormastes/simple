# Must-Check Tiering Test Plan

- Prove valid fresh compiler phase rows pass ledger validation.
- Prove stale fingerprints, failed blocking rows, missing rows, duplicate rows,
  and empty manifests fail.
- Prove TODO rows are preserved and visibly reported.
- Prove bootstrap receipt promotion is deterministic and requires all four
  compiler phase oracle lines.
- Prove bootstrap completion also runs automated rows, retains an evidence log,
  rejects self-test runner overrides in production, and preserves broad TODOs.
- Prove PASS rows without timestamps or evidence references fail validation.
- Prove the push driver directly names no native-build, QEMU, full-test, or
  benchmark command and its focused self-test stays within ten seconds.

Focused command: `sh test/01_unit/scripts/must_check_tiering_test.shs`.
