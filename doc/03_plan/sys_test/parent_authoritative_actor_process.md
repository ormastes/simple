# Parent-authoritative actor/process evidence plan

Status: source and manual authored; admitted native execution, generated mirror,
and maintenance verdict remain blocked.

## Scope

This focused plan owns the process-result portion of AC-5 and the SPipe/manual
work of AC-6 for the parent-authoritative actor/process restart. It does not
mark either criterion complete. Actor copied-reference concurrency, public
native admission failure, separate-process cancellation/backpressure, and
close wakeup/join evidence remain separate AC-5 dependencies.

Executable specification:
`test/03_system/feature/language/parent_commit_piped_result_spec.spl`.

Manual mirror:
`doc/06_spec/03_system/feature/language/parent_commit_piped_result_spec.md`.

## Frozen scenario vocabulary

The primary scenario must expose these steps in this order:

1. `Create a bounded parent-owned process session`
2. `Receive a fragmented encoded child result`
3. `Reject stale or replayed child output`
4. `Commit one validated batch at the parent`
5. `Close the child transport exactly once`

The wired helpers are `child_result_line`,
`parent_commit_frame_inbox_v1_for_generation`,
`parent_commit_piped_process_session_v1`, and
`drain_process_result_batch`. There is no optional helper path: failed setup or
receive produces a failed assertion/receipt rather than SKIP or a successful
early return.

## Scenario matrix

| Scenario | Requirements | Assertions | Acceptance boundary |
|---|---|---|---|
| Fragmented real child, replay, validated parent commit, close once | REQ-PAR-002, REQ-PAR-003, REQ-PAR-005, REQ-PAR-006, REQ-PAR-008, REQ-PAR-009; NFR-PAR-001..003, NFR-PAR-006 | positive native handle; partial-buffer observation; accepted=1; replay rejected=1; typed commit and mutation receipts; revision/root update; idempotent close; close attempts=1 | Requires admitted pure-Simple native PASS |
| Mutation after offer | REQ-PAR-002, REQ-PAR-005; NFR-PAR-003 | received bytes equal independent expected frame after producer mutates its array | Source is wired; execution verdict pending |
| Mixed valid/malformed batch | REQ-PAR-008, REQ-PAR-009; NFR-PAR-001, NFR-PAR-003 | negative mutation receipt; revision/token/root unchanged | Source is wired; execution verdict pending |

## Required evidence details

### Real process receipt

The child emits a valid `SPRF1` line in two writes and then emits the same line
again. The parent reader must observe a retained fragment before acceptance.
The generation-bound inbox admits exactly one copied frame and increments its
replay rejection counter for the duplicate.

### Parent apply, verify, and publish

The local `drain_process_result_batch` checker receives one frame and calls the
production candidate-commit boundary. Acceptance requires both the typed
commit receipt and mutation receipt. The owner snapshot must advance from
revision/token `4/400` to `5/401`, and the application payload root must change
from `[]` to `[707]` once.

### Lifecycle receipt

Natural child exit may reap the pipe during polling. If so, terminal reason is
`exited`; otherwise explicit close records `closed`. Two explicit close calls
must preserve `close_attempts == 1` in either case. The test must never require
natural exit to be mislabeled as explicit close.

## Traceability boundary

The executable carries one `# @req` line for the mapped functional and
non-functional requirements. This focused plan does not claim the following:

- stale generation is executed by the replay step (it remains focused unit
  evidence);
- actor copied-reference concurrency is exercised by this process spec;
- cancellation or backpressure is complete merely because replay rejects;
- a source-ready spec or authored manual is a native execution verdict;
- an interpreter or Rust bootstrap-seed run substitutes for native process
  transport.

## Pure-Simple runner inventory

| Candidate | Inventory result | Use |
|---|---|---|
| `bin/simple` | Absent in this worktree | None |
| `bin/release/simple` | Wrapper exists, but its bounded CLI ABI probe reaches a deployed self-hosted runtime that exits with status 139 | Blocked; preserve exact failure |
| `release/x86_64-unknown-linux-gnu/simple` | Only located deployed self-hosted binary; direct CLI probe exits with status 139 | Blocked |
| Retained Stage 2 pure-Simple artifact | `build/bootstrap/stage3/x86_64-unknown-linux-gnu/stage2-admitted/simple`; full Stage-2 build admitted 856 files with 0 failures | Used for supported direct compile/native evidence; it does not provide the Stage-4 `test`/docgen/maintenance surface |
| Rust bootstrap seed | Exists only as bootstrap tooling | Forbidden as acceptance evidence |

Direct Stage-2 execution passed copied-frame isolation and failed the remaining
three scenarios because aggregate/`Option` values were corrupted. Preserve
those assertions and repair the staged compiler; do not relabel the partial
verdict as a system PASS.

## Ordered gates

1. Repair/redeploy Stage 4 or produce a provenance-bound Stage 3/2 pure-Simple
   artifact and inventory whether it supports `test`, direct compile/native
   execution, `spipe-docgen`, and `sspec-maintain`.
2. Run the focused native system specification once. Preserve the complete
   verdict and do not rerun a green result.
3. Generate the mirror from the executable source:

   ```sh
   bin/release/simple spipe-docgen test/03_system/feature/language/parent_commit_piped_result_spec.spl --output doc/06_spec --no-index
   ```

4. Review the generated manual against the authored operator content and exact
   five-step order.
5. Run maintenance once:

   ```sh
   bin/release/simple sspec-maintain scan test/03_system/feature/language/parent_commit_piped_result_spec.spl
   ```

6. Require all seven quality scores, blocker=0, mirror PASS, traceability PASS,
   and zero stubs before AC-6 completion is proposed.
7. Merge owner integrates the evidence; a separate highest-capability reviewer
   audits the merged result. Plan acceptance from the earlier review does not
   cover this implementation/manual delta.

## Stop conditions

- A missing or crashing pure-Simple runner is a recorded blocker, not SKIP.
- Do not use the Rust seed to manufacture an acceptance verdict.
- At most three verify/fix cycles are allowed.
- Do not rerun an already-green criterion in the same session.
