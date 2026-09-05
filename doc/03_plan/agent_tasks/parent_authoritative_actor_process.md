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
| E6 Modern actor/channel evidence | `/root` | `actor_channel_authority_spec.spl`, authored mirror, focused test plan, guide/skill/wiki links | landed scheduler-domain contract | five frozen actor steps; closed typed oracle; explicit same-thread/Stage-4 boundary |

Modernization sidecars: `sspec_audit` (process source/manual),
`knowledge_audit` (guide/skill/wiki), and `final_review_prep` (truthfulness and
blocked-gate audit) were read-only and non-overlapping. `/root` remains merge
owner. The separate highest-capability E5 reviewer accepted the final
modernization delta after cancellation traceability stopped claiming
moved-source invalidation. That acceptance does not mark AC-5..AC-7 complete.

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
  - status 2026-09-05: still open, for two independent reasons. (a) No admitted
    pure-Simple full-CLI binary exists on this host — `bin/simple` has no `run`
    command, and a Rust seed cannot produce an "admitted" verdict by this plan's
    own E3 text, so ticking on a seed run would be false. (b) The oracle is RED
    anyway: `test/03_system/plan_acceptance/parent_authoritative_actor_process_spec.spl`
    `it "Obtain an admitted pure-Simple native verdict."` reports
    `accepted=0 receipt_ok=false reason=empty-process-result-batch after_revision=1`.
    The already-ticked E1 spec `parent_commit_piped_result_spec.spl` is RED the
    same way (`accepted=0 rejected=2`, 2 of 4 examples failing) while the
    identical sequence run from `fn main()` accepts and commits —
    `doc/08_tracking/bug/piped_process_frames_rejected_under_spec_runner_2026-09-05.md`.

## E2 completion checklist

- [x] Add `# @req` traceability to the executable source.
- [x] Author the mirrored operator manual without hand-claiming generation.
- [x] Add focused system-test and agent-handoff plans.
- [x] Link focused evidence from functional and NFR requirement maps.
- [x] Regenerate the manual through pure-Simple `spipe-docgen`.
  — verified 2026-09-05: `test/03_system/plan_acceptance/parent_authoritative_actor_process_spec.spl`
  `it "Regenerate the manual through pure-Simple \`spipe-docgen\`."` is GREEN.
  Closing it required fixing three real defects that made regeneration
  impossible — `spec_kw_line` and `scenario_at_is_unconditional_pending` were
  imported by `spipe-docgen` and defined in no module, and `sspec-maintain
  documentize` looked for the staged manual at a path `spipe-docgen` never
  writes (`doc/08_tracking/bug/spipe_docgen_spec_kw_line_undefined_2026-09-05.md`).
  `sspec-maintain documentize test/03_system/feature/language/parent_commit_piped_result_spec.spl`
  now reports `wrote doc/06_spec/03_system/feature/language/parent_commit_piped_result_spec.md`.
  Caveat for the reviewer: the oracle compares the docgen-OWNED content of the
  mirror (the two `<!-- sspec-maintain:* -->` wrapper blocks stripped by the same
  algorithm `documentize` used to add them), because hashing the whole committed
  file against raw docgen output can never pass while the next box's "mirror
  PASS" holds — those two blocks are where the source sha lives.
- [x] Obtain the seven-score `sspec-maintain` verdict, blocker=0, mirror PASS,
  traceability PASS, and zero stubs.
  — verified 2026-09-05: same spec, `it "Obtain the seven-score \`sspec-maintain\`
  verdict, …"` is GREEN — `blocker_count=0`, `mirror_state="current"`,
  `traceability=100`, `release_ready=true` from `analyze_sspec_pair_text` over the
  regenerated mirror. Run: `src/compiler_rust/target/debug/simple run
  test/03_system/plan_acceptance/parent_authoritative_actor_process_spec.spl`
  -> `3 examples, 1 failure` (the one failure is the "admitted native verdict"
  box above, still open).

## E3 inventory and resume

The canonical verification report records the current-source Stage-2 binary at
`build/bootstrap-restart12-current/stage2/x86_64-unknown-linux-gnu/simple`
(SHA-256 `4c2d7d7328372175260d75ffd1ee2e475d9848a1d534c73ace7a9ef1eee0b68e`).
Stage 3 remained blocked after the mandatory three fix cycles. Stage-2 direct
execution proved copied-frame isolation but exposed aggregate/`Option`
corruption in the real-child, rollback, and cancellation scenarios. The
deployed Stage-4 runtime reached through `bin/release/simple` still fails its
bounded ABI probe with status 139. Do not use the Rust bootstrap seed as an
acceptance substitute.

Commands to resume, subject to the staged runtime's supported-command
inventory, are recorded in
`doc/03_plan/sys_test/parent_authoritative_actor_process.md`.

## Acceptance

Runnable oracles for the remaining open boxes: `test/03_system/plan_acceptance/parent_authoritative_actor_process_spec.spl`
(tagged `@tag:in-development`; one `it` per open box — see
`doc/03_plan/agent_tasks/plan_remains_acceptance_2026-09-05.md`).
