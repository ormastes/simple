# Parent-authoritative actor/process evidence tasks

Status: AC-5/6 focused evidence lane in progress.

Merge owner: `/root`.

Final reviewer: a separate highest-capability reviewer after merge. The author
of this focused lane is not the final reviewer for its own merged delta.

## Frozen coordination contract

Interfaces: `ActorMailbox`, `ActorScheduler`, `ActorRef`,
`TransferEnvelopeV1`, `ProcessTransferFrameV1`,
`ParentCommitFrameInboxV1`, `ParentCommitPipedProcessSessionV1`, and
`ParentCommitOwnerV1`.

Manual steps, in order:

1. `Create a bounded parent-owned process session`
2. `Receive a fragmented encoded child result`
3. `Reject stale or replayed child output`
4. `Commit one validated batch at the parent`
5. `Close the child transport exactly once`

Helpers: `child_result_line`,
`parent_commit_frame_inbox_v1_for_generation`,
`parent_commit_piped_process_session_v1`, and
`drain_process_result_batch`.

## Ownership lanes

| Lane | Owner | Exclusive scope | Depends on | Handoff gate |
|---|---|---|---|---|
| E1 executable process evidence | `/root/highest_review` for the pre-merge authoring task | `test/03_system/feature/language/parent_commit_piped_result_spec.spl` | landed process inbox/session and parent candidate-commit APIs | five exact steps; real pipe; no SKIP/successful early return; copied isolation; rollback; close-once receipt |
| E2 manual and traceability | `/root/highest_review` for the pre-merge authoring task | focused manual, system-test plan, task handoff, requirement evidence links | E1 source contract | operator-quality mirror; explicit blocked-generation status; AC/REQ mapping |
| E3 staged tooling inventory | `/root/highest_review` for inventory only; merge owner resumes execution | read-only Stage 4/3/2 command/provenance inventory | E1 source-ready state | exact supported/unsupported command report; no Rust seed acceptance |
| E4 merge/integration | `/root` | integrate focused files with concurrent actor/process production and documentation lanes | E1..E3 | resolve API drift, run admissible gates once, retain blockers |
| E5 final audit | separately assigned highest-capability reviewer | read-only merged AC-5/6 evidence review | E4 | ACCEPT/REJECT with exact findings; no underlying-feature done mark without all AC gates |

Sidecar lanes: **N/A for this focused authoring delta**. The best-capability
merge owner had already frozen the interface, step, and helper vocabulary, and
the bounded task is performed directly. Earlier actor/process read-only audits
do not substitute for E5 review of the merged implementation/manual change.

## E1 completion checklist

- [x] Replace `piped_process_extern_available` and its SKIP/return path.
- [x] Use the real existing frame codec, inbox, session, and owner APIs.
- [x] Wire all four frozen helpers.
- [x] Add all five frozen steps exactly once and in order.
- [x] Assert mutation-after-offer copied isolation.
- [x] Assert a mixed valid/malformed batch preserves both roots.
- [x] Assert natural exit reason separately from explicit close and retain
  `close_attempts == 1` across repeated close.
- [ ] Obtain an admitted pure-Simple native verdict.

## E2 completion checklist

- [x] Add `# @req` traceability to the executable source.
- [x] Author the mirrored operator manual without hand-claiming generation.
- [x] Add focused system-test and agent-handoff plans.
- [x] Link focused evidence from functional and NFR requirement maps.
- [ ] Regenerate the manual through pure-Simple `spipe-docgen`.
- [ ] Obtain the seven-score `sspec-maintain` verdict, blocker=0, mirror PASS,
  traceability PASS, and zero stubs.

## E3 inventory and resume

The lane produced the admitted Stage-2 pure-Simple binary at
`build/bootstrap/stage3/x86_64-unknown-linux-gnu/stage2-admitted/simple`.
Stage 3 remained blocked after the mandatory three fix cycles. Stage-2 direct
execution proved copied-frame isolation but exposed aggregate/`Option`
corruption in the real-child, rollback, and cancellation scenarios. The
deployed Stage-4 runtime reached through `bin/release/simple` still fails its
bounded ABI probe with status 139. Do not use the Rust bootstrap seed as an
acceptance substitute.

Commands to resume, subject to the staged runtime's supported-command
inventory, are recorded in
`doc/03_plan/sys_test/parent_authoritative_actor_process.md`.
