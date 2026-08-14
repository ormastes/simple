# Parent-authoritative piped child results

> Status: authored manual mirror; pure-Simple generation and maintenance
> verdicts are pending. This document does not claim a native SPipe PASS.

## At a glance

| Item | Value |
|---|---|
| Executable source | `test/03_system/feature/language/parent_commit_piped_result_spec.spl` |
| Audience | Language/runtime maintainers and verification operators |
| Primary boundary | Real piped child output to bounded parent-owned validation and commit |
| Scenarios | Real fragmented/replayed child result; copied-frame isolation; mixed-batch rollback |
| Acceptance runtime | An admitted pure-Simple Stage 4, Stage 3, or Stage 2 runtime with the required commands |
| Current execution state | Stage-2 copied isolation PASS; three scenarios blocked by aggregate/`Option` corruption; Stage 4 exits 139 |

## Purpose

This manual explains how to run and interpret the focused parent-authoritative
process-result specification. The executable scenario proves behavior only
when it receives an admitted native verdict. Source inspection, the presence
of this mirror, or a Rust bootstrap-seed result is not a replacement for that
verdict.

The primary flow launches `/bin/sh` through
`ParentCommitPipedProcessSessionV1`. The child writes one armored `SPRF1`
result in two pieces, pauses between pieces, and then writes the same frame a
second time. The parent must bound the partial text, accept exactly one frame,
reject the replay, validate and apply one candidate root under
`ParentCommitOwnerV1`, and release the native process handle once.

## Requirements and evidence map

| Requirement | Observable evidence in this specification | Boundary |
|---|---|---|
| REQ-PAR-002 | Encoded-copy frame, bounded inbox admission, and mutation-after-offer isolation | Copy/transfer safety |
| REQ-PAR-003 | Child-created result is decoded before parent-owned application | Child result only |
| REQ-PAR-005 | Only armored bytes and typed envelopes cross the process boundary | No process-local pointers |
| REQ-PAR-006 | Finite inbox capacity, partial-line retention, replay rejection | Bounded transport/backpressure |
| REQ-PAR-008 | Parent candidate apply/verify receipt and published root assertions | Sole parent commit |
| REQ-PAR-009 | Task ID, payload token, revision, and snapshot-token assertions | Deterministic commit |
| NFR-PAR-001 | Canonical task/result receipt values | Determinism |
| NFR-PAR-002 | Capacity, one-frame intake, and bounded reader state | Bounded memory |
| NFR-PAR-003 | Typed codecs reject malformed bytes before publication | Fail closed |
| NFR-PAR-006 | Explicit native/tooling blocker and no seed substitution | Parity reporting |

This file contributes to AC-5 and AC-6. It does not by itself complete AC-5:
the broader acceptance criterion also requires actor public-surface,
cancellation, backpressure, and separate-process evidence outside this focused
flow. It does not complete AC-6 until pure-Simple doc generation and the full
`sspec-maintain` scorecard pass.

## Preconditions

1. Use a provenance-recorded pure-Simple binary. Do not use
   `src/compiler_rust/target/bootstrap/simple` as acceptance evidence.
2. The runtime must support the piped process facade used by
   `parent_commit_piped_process_session_v1`.
3. `/bin/sh` and `sleep` must be available to the test process.
4. Run from the repository root with `SIMPLE_LIB=src` when required by the
   selected staged runtime.
5. Keep the five step labels and four frozen helpers unchanged; tooling and
   reviewers use them as the stable manual contract.

## Primary scenario contract

### 1. Create a bounded parent-owned process session

The setup creates the sole long-lived `ParentCommitOwnerV1`, obtains its next
locked process generation, calls `child_result_line`, binds the inbox through
`parent_commit_frame_inbox_v1_for_generation`, and starts the child through
`parent_commit_piped_process_session_v1`. A non-positive generation or process
handle is a test failure; there is no skip or successful early return.

Expected observations:

- the process handle is positive;
- the session is initially open;
- the inbox has a finite four-frame admission ceiling and is bound to the
  session generation in executable setup.

### 2. Receive a fragmented encoded child result

The shell emits half of the armored line, pauses, then emits the remainder and
a newline. The executable polls with a finite line and iteration budget.

Expected observations:

- at least one poll exposes retained partial bytes before acceptance;
- exactly one frame is accepted;
- exactly one copied frame remains in the parent inbox;
- the reader records a positive partial-buffer high-water mark.

Failure meaning:

- no retained fragment indicates the platform did not expose the intended
  split and is not accepted as fragmented-read evidence;
- more than one accepted frame indicates replay admission;
- zero accepted frames indicates pipe, codec, generation, or route failure.

### 3. Reject stale or replayed child output

After the valid line, the child writes the identical generation/region frame.
The lifetime-bounded replay table must reject it.

Expected observations:

- one accepted frame and one rejected replay are reported;
- the stale/session-generation rejection counter stays zero;
- inbox depth stays one, so a rejected duplicate never consumes capacity.

This scenario exercises replay, not a stale-generation child. The focused
generation-mismatch unit remains separate evidence and must not be represented
as executed by this step.

### 4. Commit one validated batch at the parent

The frozen local checker `drain_process_result_batch` transfers the admitted
frame to `commit_process_result_frames_with_candidate`. The candidate root is
`[707]`, matching the decoded ordered payload token.

Expected observations:

- the typed commit receipt is successful and orders task `7` with token `707`;
- the mutation receipt advances revision `4` to `5`;
- the application payload root changes once from `[]` to `[707]`;
- the owner snapshot token becomes `401`;
- the inbox is empty after transfer.

The helper fails closed by submitting an empty batch if receive fails; that
path cannot produce a successful receipt.

### 5. Close the child transport exactly once

Polling may reap the child naturally before explicit close. Both natural and
explicit terminal paths are valid, but the native close attempt count must be
exactly one. Repeated `close()` calls must return the recorded result without
calling the native close path again.

Expected observations:

- the session is closed and not alive;
- `close_attempts == 1` after two explicit close calls;
- `terminal_reason == "exited"` when `naturally_exited` is true;
- otherwise `terminal_reason == "closed"`.

## Supporting scenarios

### Copied-frame isolation

The producer offers a valid encoded frame and then mutates byte zero of its
local array. The received parent copy must still equal a separately encoded
expected frame. This closes the mutation-after-offer source-evidence gap; an
admitted runtime result is still required for an execution verdict.

### Mixed-batch rollback

The owner receives one valid frame and one malformed byte array in the same
candidate batch. Decode must fail before publication. The negative mutation
receipt, revision `4`, snapshot token `800`, and empty application root must
all remain observable afterward.

## Failure diagnostics

| Symptom | Likely boundary | Operator action |
|---|---|---|
| Process handle is not positive | Native piped-process facade or child command | Record the exact runtime provenance and stderr; do not convert to SKIP |
| Fragment assertion fails | Pipe-read scheduling or blocking read behavior | Preserve the failed verdict and inspect native read semantics |
| Accepted count is zero | Text framing, route, generation, or codec | Compare reader reason/counters with focused hostile-stream units |
| Replay counter is zero | Deferred suffix, process reap, or replay identity | Inspect whether both lines reached the reader before terminal close |
| Mutation receipt is false | Candidate root or typed result mismatch | Inspect receipt reason; do not publish or reinsert the frame |
| `close_attempts` differs from one | Reap/close lifecycle regression | Treat as a lifecycle failure even if repeated close returns true |

## Commands and current blocker

Intended execution:

```sh
SIMPLE_LIB=src bin/release/simple test test/03_system/feature/language/parent_commit_piped_result_spec.spl --mode=native
```

Intended mirror generation:

```sh
bin/release/simple spipe-docgen test/03_system/feature/language/parent_commit_piped_result_spec.spl --output doc/06_spec --no-index
```

Intended maintenance gate:

```sh
bin/release/simple sspec-maintain scan test/03_system/feature/language/parent_commit_piped_result_spec.spl
```

This lane produced the provenance-admitted Stage-2 pure-Simple binary at
`build/bootstrap/stage3/x86_64-unknown-linux-gnu/stage2-admitted/simple`.
Direct execution with that binary passed copied-frame isolation, while the
fragmented child, rollback, and cancellation paths exposed aggregate/`Option`
corruption and remain failed evidence. Stage 3 stopped after the mandatory
three fix cycles, and the available `bin/release/simple` Stage-4 wrapper still
exits 139 during its bounded CLI ABI probe. Doc generation and maintenance
therefore have no admitted verdict in this revision.

## Maintenance acceptance

Before AC-6 can be called complete, regenerate this mirror from the executable
source and review the generated result as an operator manual. Then require all
seven `sspec-maintain` quality scores, zero blockers, mirror PASS, traceability
PASS, and zero stubs. Replace this status note with the actual command,
runtime provenance, and verdict; do not hand-enter a PASS.

## Review checklist

- [ ] Admitted pure-Simple native scenario PASS is attached.
- [ ] Exactly five frozen step labels are present and ordered.
- [ ] `child_result_line`, `parent_commit_frame_inbox_v1_for_generation`,
  `parent_commit_piped_process_session_v1`, and
  `drain_process_result_batch` remain wired.
- [ ] No SKIP or successful early-return path exists.
- [ ] Natural exit preserves `terminal_reason == "exited"`.
- [ ] Repeated close leaves `close_attempts == 1`.
- [ ] Generated mirror matches the executable source.
- [ ] `sspec-maintain` reports seven acceptable scores and no blocker.

## Related artifacts

- Requirements: `doc/02_requirements/feature/parallel_ownership_memory_layout.md`
- NFRs: `doc/02_requirements/nfr/parallel_ownership_memory_layout.md`
- Architecture: `doc/04_architecture/language/parallel_ownership_model.md`
- Detail design: `doc/05_design/language/concurrency/parent_commit_parallel_apps.md`
- Focused test plan: `doc/03_plan/sys_test/parent_authoritative_actor_process.md`
- Agent handoff: `doc/03_plan/agent_tasks/parent_authoritative_actor_process.md`
