# sspec: hollow-expect provisional text clobbers real failure message (2026-08-19)
## Closed 2026-09-16 — ...ng expectation is wrong/misleading. ## Fix sketch On the matcher-pass path at bdd.rs:1134,

Reviewed in the 2026-09-16 bug-ledger normalization pass; classification is
bookkeeping from in-file evidence, not a re-run of the repro. Re-open with a
fresh dated repro if the symptom returns.

**Status:** FIXED (2026-11-11 runner10 lane — root-cause fix landed in the Rust seed and verified contained in the tracked seed binary)
**Site:** `src/compiler_rust/compiler/src/interpreter_call/bdd.rs:1134`

## Mechanism

When a matcher PASSES, the code clears the BDD failure *flag* but does not clear
`BDD_FAILURE_MSG`. The hollow-expect detector writes a provisional message
("hollow expect" text) before matcher evaluation; on the pass path that
provisional text is left standing in `BDD_FAILURE_MSG`. When a *later* expect in
the same test genuinely fails, the reporter can surface the stale provisional
hollow-expect text instead of (or clobbering) the real failure's message, so the
diagnostic shown for the failing expectation is wrong/misleading.

## Fix sketch

On the matcher-pass path at bdd.rs:1134, clear `BDD_FAILURE_MSG` alongside the
failure flag (or scope the provisional hollow-expect message so it is consumed
or discarded per-expect rather than per-test).

## Found while

Debugging closure_captured_instance_loses_method_self_mutation_2026-08-19 — the
secondary defect made the primary failure's message unreadable.


## Triage 2026-11-03 (tr-sspec lane)
Verdict: FIXED in source. `src/compiler_rust/compiler/src/interpreter_call/bdd.rs` now keeps the
provisional hollow-expect message in its own slot `BDD_PROVISIONAL_MSG` (bdd.rs:134), cleared per
example (:990) and promoted only when `BDD_FAILURE_MSG` is still None (:1076), so it can no longer
clobber a real failure. Sibling record: spec_runner_provisional_truthy_message_clobbers_real_failure_2026-08-21.
Seed rebuild not run in this lane; verify on next seed build.

## 2026-11-11 — runner10 lane verdict: FIXED (verified in tracked seed)

Re-verified fresh at base 79d5af6723f6 (no re-runs of prior green checks):

1. **Fix ancestry.** The provisional-message separation
   (`BDD_PROVISIONAL_MSG` slot at bdd.rs:212, cleared per example :155/:990/:1076,
   promoted only when `BDD_FAILURE_MSG` has no summary :1158-1165 — "a
   provisional message is a FALLBACK, never a replacement") was introduced by
   merge 9e7e7a526edb (PR #7597, 2026-11-07). `git merge-base --is-ancestor
   9e7e7a526edb 46fe8f6b6def` confirms the fix IS an ancestor of the tracked
   seed binary commit, and `git show 46fe8f6b6def:...bdd.rs` shows all 9
   `BDD_PROVISIONAL_MSG` sites — the deployed `bin/simple.exe` contains the
   fix (the 2026-11-03 tr-sspec note's "verify on next seed build" condition
   is now met by lineage).
2. **Old-vs-new read.** Pre-fix, a passing matcher's provisional text was
   left standing in the `BDD_FAILURE_MSG` slot, so a later real failure in
   the same example could be reported with the stale "hollow expect" text.
   Current code keeps the provisional in its own slot and reports it only
   when no real matcher failure was recorded — the clobber path is gone by
   construction.

Residual: no SPipe-level regression spec asserts the reported *message
text* (that needs a runner-in-runner child harness, expensive and
child-exit-plumbing-sensitive on the Windows interpreted driver; the
mechanism is covered by the slot design above plus bdd.rs's 8 Rust unit
tests). Follow-up harness spec recorded here, not blocking the flip.
