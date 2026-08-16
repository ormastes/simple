# Parent-authoritative actor/process evidence plan

Status: Modern SSpec source and authored manual updated; admitted native
execution, generated mirror, and maintenance verdict remain blocked.

## Scope

This focused plan owns the process-result portion of AC-5 and the SPipe/manual
work of AC-6 for the parent-authoritative actor/process restart. It does not
mark either criterion complete. The source now contributes live
cancellation/revocation assertions, but actor copied-reference concurrency,
public native admission failure, separate-process backpressure, and provider
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
| Fragmented real child, replay, validated parent commit, close once | REQ-PAR-002/003/005/006/008/009; NFR-PAR-001..003 | positive native handle; partial-buffer observation; accepted=1; replay rejected=1; typed commit and mutation receipts; revision/root update; idempotent close; close attempts=1; closed typed oracle | Partial: one result cannot prove completion-order determinism or full portability |
| Mutation after offer | REQ-PAR-002/005; NFR-PAR-003 | received bytes equal independent expected frame after producer mutates its array | Partial encoded-copy isolation |
| Mixed valid/malformed batch | REQ-PAR-008/009; NFR-PAR-001/003 | negative mutation receipt; revision/token/root `[600]` unchanged | Partial atomic rollback |
| Live child cancellation | REQ-PAR-006; NFR-PAR-002/003 | accepted frame revoked; inbox closed; cancellation terminal; close attempts=1 | Partial lifecycle evidence; moved-source invalidation, PID reuse, and provider parity remain open |

## Traceability matrix

| Requirement | Executable cases | Mirror | Coverage |
|---|---:|---|---|
| REQ-PAR-002/003/005 | primary + copied isolation | `doc/06_spec/03_system/feature/language/parent_commit_piped_result_spec.md` | Partial: encoded child result only |
| REQ-PAR-006 | primary + cancellation | same mirror | Partial: finite ingress/replay/revoke, not full backpressure matrix |
| REQ-PAR-008/009 | primary + rollback | same mirror | Partial: application token-root adapter, not arbitrary schema/determinism permutations |
| NFR-PAR-001..003 | primary + rollback + cancellation | same mirror | Partial |
| NFR-PAR-006 | 0 executable cases | documented blocker only | Missing; not tagged as executed coverage |

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
| Retained Stage 2 pure-Simple artifact | `build/bootstrap-restart12-current/stage2/x86_64-unknown-linux-gnu/simple`; SHA-256 `4c2d7d7328372175260d75ffd1ee2e475d9848a1d534c73ace7a9ef1eee0b68e` in the canonical report | Used only for supported direct compile/native evidence; it does not provide the Stage-4 `test`/docgen/maintenance surface |
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

## Modern evidence and manual policy

- Primary scenario: visible with the five frozen steps in order.
- Copied isolation, rollback, and cancellation: supporting/detail scenarios;
  visible as concise manual sections and folded executable source after docgen.
- Evidence kind: protocol/domain observation under closed schema
  `parent-commit-piped-result/v1`.
- Oracle: eleven independent `check_exact` fields plus direct branch assertion
  for `exited` versus `closed`.
- Provenance: exact pure-Simple Stage-4 path/hash, command, environment, source
  digest, and generated mirror digest are required; currently missing because
  the bounded ABI probe blocks execution/docgen/maintenance.
- Pass requires native scenario success, zero docgen stubs, all seven
  maintenance scores above threshold, blocker=0, mirror PASS, and traceability
  PASS. A source-only comparison is never promoted to execution evidence.

## Stop conditions

- A missing or crashing pure-Simple runner is a recorded blocker, not SKIP.
- Do not use the Rust seed to manufacture an acceptance verdict.
- At most three verify/fix cycles are allowed.
- Do not rerun an already-green criterion in the same session.
