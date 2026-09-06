# Real-child process frames are REJECTED under the spec runner but ACCEPTED from `fn main()` — identical code

Date: 2026-09-05. Found while trying to close
`doc/03_plan/agent_tasks/parent_authoritative_actor_process.md` E1 box
"Obtain an admitted pure-Simple native verdict".

## Symptom

The parent-owned piped-process transport reads the child's output and then
rejects every frame, instead of admitting the first and rejecting only the
replay.

`test/03_system/feature/language/parent_commit_piped_result_spec.spl`
(whose plan checkboxes are already `[x]`) is RED:

```
fragmented evidence accepted=0 rejected=2 depth=0 fragment=true closed=true
  ✗ should validate, commit, and close one fragmented child result
    expected 7 check(s) failed to equal 11 check(s) passed
cancel evidence accepted=0 depth=0 cancelled=true closed=true alive=false attempts=1 reason=cancelled
  ✗ should cancel a live child and revoke its accepted result
    expected empty to equal closed
4 examples, 2 failures
```

`fragment=true` and `rejected=2` prove the pipe WAS read and two complete
frames WERE reassembled — the failure is in envelope admission, not transport.
The two scenarios that do not spawn a child (copied-frame retention, mixed
valid/malformed rollback) both PASS, which localises it further.

## The discriminating experiment

The exact same call sequence — `parent_commit_owner_v1(parallel_commit_state_v1(1, 900))`,
`issue_process_session_generation()`, `parent_commit_frame_inbox_v1_for_generation`,
`process_transfer_text_line_encode`, `parent_commit_piped_process_session_v1("/bin/sh", …)`,
poll loop — run from a plain `fn main()` program instead of inside
`describe`/`it` **succeeds**:

```
generation=1788579747978197
handle=27749
accepted_total=1 polls=3
received.ok=true reason=
receipt_ok=true
after_revision=2
```

So the defect is not in the sequence or in the child script. It is
context-dependent: under the spec runner the frames are refused, from a
top-level program they are admitted.

## Leading hypothesis (not yet proven)

Both frames being rejected — rather than one admitted and one rejected as a
replay — is the signature of a SESSION-generation mismatch, not of replay
detection: the generation the frames were built with does not equal the
generation the inbox validates against. `issue_process_session_generation()`
returns a microsecond-scale i64 (~1.79e15). A path that round-trips it through
an erased or floating representation between the `it` body and the codec would
reproduce exactly this. `intake_stats.rejected_session_frames` vs
`rejected_replay_frames` (asserted at
`parent_commit_piped_result_spec.spl:184-185`) is the next measurement to take.

## Impact

- E1 checkbox "Obtain an admitted pure-Simple native verdict" cannot be closed:
  its acceptance oracle
  (`test/03_system/plan_acceptance/parent_authoritative_actor_process_spec.spl`,
  `it "Obtain an admitted pure-Simple native verdict."`) fails with
  `accepted=0 receipt_ok=false reason=empty-process-result-batch after_revision=1`.
- The plan's already-ticked E1 boxes rest on a spec that is currently RED on
  this host. Left RED deliberately per `.claude/rules/testing.md`; no assertion
  was weakened.

## Unblock condition

Either a root cause for the context-dependent rejection, or a run on the
admitted pure-Simple Stage-4 binary the checkbox actually names. Verified here
with `src/compiler_rust/target/debug/simple` (current-source Rust seed, built
2026-09-04 18:13) — the sanctioned `bin/release/aarch64-apple-darwin/simple_seed`
(2026-07-25) cannot parse current stdlib source at all, see
`doc/08_tracking/bug/stale_deployed_binaries_reject_current_language_sspec_scorer_unrunnable_2026-09-05.md`.
