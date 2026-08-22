# Must-Check Tiering Test Plan

- Prove valid fresh compiler phase rows pass ledger validation.
- Prove stale fingerprints, failed blocking rows, missing rows, duplicate rows,
  and empty manifests fail.
- Prove TODO rows are preserved and visibly reported.
- Prove bootstrap receipt promotion is deterministic and requires all four
  compiler phase oracle lines.
- Prove bootstrap completion also runs automated rows, retains an evidence log,
  binds them to the exact validated Stage 4 candidate despite a conflicting
  ambient `SIMPLE_BINARY`, rejects self-test runner overrides in production,
  and preserves broad TODOs.
- Prove the existing interpreter/JIT/native differential producer is owned by
  the bootstrap tier and cannot run from the lightweight push path.
- Prove PASS rows without timestamps or evidence references fail validation.
- Prove unowned rows, TODO rows without an unblock condition, and PASS rows
  with a pending unblock condition fail validation.
- Prove the bootstrap producer's generated ledger is committed and accepted by
  the real pre-push ref-input consumer without manually fabricating PASS state.
- Prove the push driver directly names no native-build, QEMU, full-test, or
  benchmark command and its focused self-test stays within ten seconds.
- Prove identical ref updates execute the tree gate once, more than two unique
  updates fail closed, and the push tree gate receives bounded `--push-tip`
  mode while its exhaustive fixture campaign is bootstrap-owned.
- Prove production ledger validation rejects absolute external evidence,
  parent traversal, and aggregate evidence beyond 64 MiB before hashing.
- Prove `--ref` rules evaluation ignores a hostile dirty `rules.sdl`, parses the
  committed registry, and fingerprints that policy in producer and consumer.
- On a native Windows host, create two linked worktrees, run
  `powershell -File scripts/setup/install-must-check-hooks.ps1 -Install` in the
  first, then `-Check` and `sh scripts/check/check-hook-installation.shs` from
  the second. Retain the hook hash and both verdicts; until then
  `windows-hook-installation` remains TODO.

Focused command: `sh test/01_unit/scripts/must_check_tiering_test.shs`.

## Traceability

| Requirement | Executable evidence | Scenarios | Status |
|---|---|---:|---|
| REQ-MCT-001, REQ-MCT-003 | `test/03_system/check/must_check_tiering_spec.spl` | push validator | Source present; Stage-4 execution pending |
| REQ-MCT-002, REQ-MCT-005 | `test/03_system/check/must_check_tiering_spec.spl` | bootstrap producer | Source present; Stage-4 execution pending |
| REQ-MCT-004, REQ-MCT-006 | `test/03_system/check/must_check_tiering_spec.spl` | producer-to-consumer and installer | Shell fixture PASS; Stage-4 SSpec pending |
| REQ-MCT-006 Windows | `scripts/setup/install-must-check-hooks.ps1` | linked-worktree install/check | TODO: native Windows host evidence required |

The manual mirror is
`doc/06_spec/03_system/check/must_check_tiering_spec.md`. Regenerate it with
the exact admitted Stage-4 CLI; this worktree has no `bin/simple`, so seed
substitution is forbidden.
