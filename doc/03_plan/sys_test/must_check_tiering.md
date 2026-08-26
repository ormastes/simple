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
- Prove unowned rows, TODO rows without an unblock condition, and PASS rows
  with a pending unblock condition fail validation.
- Prove the bootstrap producer's generated ledger is committed and accepted by
  the real pre-push ref-input consumer without manually fabricating PASS state.
- Prove the push driver directly names no native-build, QEMU, full-test, or
  benchmark command and its focused self-test stays within ten seconds.

Focused command: `sh test/01_unit/scripts/must_check_tiering_test.shs`.

## Traceability

| Requirement | Executable evidence | Scenarios | Status |
|---|---|---:|---|
| REQ-MCT-001, REQ-MCT-003 | `test/03_system/check/must_check_tiering_spec.spl` | push validator | Source present; Stage-4 execution pending |
| REQ-MCT-002, REQ-MCT-005 | `test/03_system/check/must_check_tiering_spec.spl` | bootstrap producer | Source present; Stage-4 execution pending |
| REQ-MCT-004, REQ-MCT-006 | `test/03_system/check/must_check_tiering_spec.spl` | producer-to-consumer and installer | Shell fixture PASS; Stage-4 SSpec pending |

The manual mirror is
`doc/06_spec/03_system/check/must_check_tiering_spec.md`. Regenerate it with
the exact admitted Stage-4 CLI; this worktree has no `bin/simple`, so seed
substitution is forbidden.
