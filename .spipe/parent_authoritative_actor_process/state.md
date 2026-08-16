# Feature: parent-authoritative-actor-process

## Raw Request

`$sp_dev with pherallel agents with guide and higher model review complete the plan doc`

## Task Type

todo

## Refined Goal

Complete every Restart12 actor/process acceptance item in the canonical parallel-ownership plan with production actor/channel ownership, bounded process transport, executable evidence, current operator guidance, and independent highest-capability review.

## Acceptance Criteria

- AC-1: Public actor send/ask/stop routes through one scheduler and mailbox authority; copied references reject post-close admission, and safe actor/channel transport cannot carry unchecked heap values or child-local pointers.
- AC-2: Process results traverse only bounded canonical `SPRF1`/`SPRS` encoded-copy framing; split/coalesced reads, malformed/non-ASCII/oversize input, frame/byte backpressure, generation mismatch, and replay fail closed.
- AC-3: `ParentCommitOwnerV1` is the sole mutable root owner; it validates the complete child-created result batch, applies deterministic ordering/conflict policy, publishes once, and leaves state unchanged on any failed batch.
- AC-4: Child lifecycle is parent-owned and bounded: cancellation/close is observable, accepted process handles close exactly once, and failed/stale/rejected results are never reinserted or implicitly retried.
- AC-5: Focused unit/integration/system SSpec covers copied isolation, actor close/backpressure, split/coalesced process reads, replay/session rejection, deterministic commit, rollback, and real separate-process delivery with non-vacuous assertions and requirement traceability.
- AC-6: The mirrored `doc/06_spec` manual is generated through pure-Simple SPipe with zero stubs, reads as an operator manual, and the changed spec passes `sspec-maintain scan` across all seven scores with no blocker or mirror failure.
- AC-7: The deployed self-hosted Stage 4 runtime passes the focused native process spec once; changed core/lib surfaces also pass required compiler/lib/MCP/LSP checks, direct-runtime audits, lint, duplication, and applicable concurrency/resource-model evidence.
- AC-8: Knowledge is current in the canonical research/requirements/architecture/design/plan, `doc/07_guide/language/parallel_apps.md`, feature expert `doc/00_llm_process/feature_expert/parallel_ownership/skill.md` (create or select the closest canonical feature entry), layer expert for actor/process runtime, and tracked bug records for every unresolved gap. Workflow/skill/command trees are N/A unless this lane changes their contracts.
- AC-9: A normal/highest-capability reviewer audits AC-1..AC-8 against current source, executable evidence, manual quality, exclusions, and plan done marks; the canonical plan records each item PASS or a still-open blocker without overclaim.

## Scope Exclusions

Storage-layout lowering, borrow analysis, GPU/device transport, and unrelated MDSOC pilots remain outside this actor/process completion lane unless required to prove an actor/process invariant.

## Cooperative Review

- Sidecar `actor_audit`: actor/channel authority, typed boundary, lifecycle, and evidence gaps.
- Sidecar `process_audit`: framed process/session/replay, parent commit rollback, SPipe/manual, and guide gaps.
- Merge owner: `/root`.
- Final reviewer: separate `gpt-5.6-sol` highest-capability review after integration.
- Frozen interfaces: `ActorMailbox`, `ActorScheduler`, `ActorRef`, `TransferEnvelopeV1`, `ProcessTransferFrameV1`, `ParentCommitFrameInboxV1`, `ParentCommitPipedProcessSessionV1`, `ParentCommitOwnerV1`.
- Manual flow steps: `Create a bounded parent-owned process session`; `Receive a fragmented encoded child result`; `Reject stale or replayed child output`; `Commit one validated batch at the parent`; `Close the child transport exactly once`.
- Setup/checker helpers: `child_result_line`, `parent_commit_frame_inbox_v1_for_generation`, `parent_commit_piped_process_session_v1`, `drain_process_result_batch`.
- Placeholders must use `assert(false)` or `fail(...)`; silent no-op helpers are forbidden.
- Generated-manual review owner: final highest-capability reviewer.

## Phase

verify-blocked

## Log

- dev: Created state file with 9 acceptance criteria (type: todo).
- cooperative review: `actor_audit` and `process_audit` supplied source-backed
  gap matrices; `/root` merged them into the canonical plan and guide.
- highest-capability review: `ACCEPT` for plan/document completion after five
  factual/dependency corrections; underlying implementation remains open.
- modern SSpec continuation: added closed typed evidence to the process flow and
  authored a separate scheduler-owned actor/channel system scenario plus mirror,
  guide, and test plan. Generation and native execution remain blocked by the
  deployed Stage-4 bounded test ABI probe; AC-5..AC-7 stay open.
- modernization review: the separate highest-capability reviewer accepted the
  corrected partial delta after cancellation stopped claiming moved-source
  invalidation; this is not an underlying feature PASS.
- shortened non-Phase-4 continuation: repaired the actor mailbox indentation
  parse defect and normalized `runtime_memtrack.c` to LF. The admitted Stage-2
  compile now passes the mailbox and stops later at the tracked actor-spawn
  flat-AST/compiled `str.clear` gap. Static guards pass; the obsolete `STP1`
  sibling branch was inspected and deliberately not merged.
