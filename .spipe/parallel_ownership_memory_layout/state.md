# Feature: parallel-ownership-memory-layout

## Raw Request

`$sp_dev update/create pherallel agents plan and impl memory efficient simple.`

Supporting artifacts supplied in this thread:

- `doc/01_research/language/parallel_ownership_and_storage_layout_research_2026-08-12.md`
- `doc/03_plan/language/parallel_memory_mdsoc_plus_parallel_agents_2026-08-12.csv`

## Task Type

feature

## Refined Goal

Establish the frozen ownership-transfer, storage-layout, and parent-authoritative parallel-commit foundations that make Simple's memory-efficient parallel applications safe, deterministic, and implementable through staged work packages.

## Acceptance Criteria

- AC-1: A baseline/collision census records the current commit identity, authoritative existing ownership/placement/layout/commit names, and any conflicts with the proposed V1 contracts.
- AC-2: Versioned transfer, storage-layout, and parallel-commit contracts have one canonical owner, deterministic serialization/hash rules, and focused malformed-input, collision, and deterministic-order evidence.
- AC-3: Resolved memory and parallel policy has explicit precedence, cannot lower the active assurance profile, and maps every critical ownership/transport/commit rule to a stable diagnostic.
- AC-4: Parent-to-child transfer, child-created result transfer, frozen sharing, dynamic value classification, bounded mailbox behavior, and parent commit have executable behavior or a retained blocker with a precise owner and resume gate; no safe boundary transmits a raw process-local pointer.
- AC-5: Borrow/region analysis treats unknown dynamic indices as overlapping until a disjointness proof exists, and it cannot justify transfer or backend alias evidence from an unproven overlap claim.
- AC-6: Storage-layout work preserves logical `T[]` semantics across reference AoS and any enabled transformed representation, rejects ABI/wire/MMIO transformations without an explicit boundary, and records layout policy/receipt identity.
- AC-7: The MDSOC+ integration route makes transfer, layout, and commit policy visible to a real stage and detects a bypass of the selected route.
- AC-8: At least one thread/process parent-commit pilot uses immutable input, bounded transfer, child-created output, deterministic parent commit, failure/cancellation cleanup, and real—not mock—transport evidence.
- AC-9: Knowledge updates are synchronized: research, requirements, architecture, design, plan, guide, feature/layer skills, generated/manual specs where executable behavior changes, and open bug records for all unfixed blockers. Documentation must distinguish proposed, reachable, and blocked behavior.
- AC-10: Verification records each acceptance criterion once with focused evidence; unavailable host/device rows remain explicit blocked work with an owner, prerequisite, exact resume command, retained artifacts, and final reviewer. The umbrella goal is not complete until all required rows pass.

## Scope Exclusions

- No new mandatory ownership or lifetime grammar.
- No blanket SoA rewrite of generic dynamic arrays.
- No claim that process-local pointers, unbounded queues, or raw `Any` transport are safe.
- No release, tag, or push in this lane unless separately requested after verification PASS.

## Cooperative Review

Broad lane. Sidecars: N/A in this turn because shared contract names and acceptance vocabulary must be set by the integration owner before parallel implementation work. Merge owner: `/root`. Final reviewer: normal/highest-capability reviewer after each wave. Shared interfaces: `TransferEnvelopeV1`, `StorageLayoutPlanV1`, `ParallelCommitPort`, `ResolvedParallelPolicyV1`, `ResolvedMemoryPolicyV1`. Future SSpec helper names: `step_create_parent_snapshot`, `step_send_child_result`, `step_commit_results_in_order`, `check_no_raw_pointer_transport`. Fail-fast placeholders: `fail("parallel ownership contract not wired")`. Generated-manual review owner: `/root` until a dedicated documentation lane is assigned.

## Phase

dev-done

## Log

- dev: Created state file with 10 acceptance criteria (type: feature).
- design: Added selected feature/NFR requirements, MDSOC ownership architecture,
  detail design, and agent-lane plan. Existing placement and mutation contracts
  are common dependencies and must not be redeclared.
- impl: Started WP-01 with `TransferEnvelopeV1` vocabulary and focused unit
  contract coverage. The available `bin/simple` reports itself as a bootstrap
  seed; focused test/lint invocations produced repository-wide seed warnings
  without a trustworthy self-hosted PASS verdict. Resume after a fresh admitted
  Stage 4 CLI is available with:
  `bin/simple test test/01_unit/common/structural/transfer_contract_spec.spl --mode=interpreter`.
- impl: Added the remaining Wave 0 common vocabulary surfaces:
  `StorageLayoutPlanV1` separates physical storage from spatial layout and
  pins external ABI layout; `ResultEnvelopeV1` and `ParallelCommitPort` define
  canonical ordering/conflict inputs. Focused structural tests were added for
  each. `git diff --check` passes and the new files contain no stub markers.
  Runtime transfer codecs, bounded mailboxes, policy resolution, and actual
  parent commit are still unimplemented Wave 1 work, not implied by these
  contract records.
- impl: Added WP-04 `ResolvedParallelPolicyV1`. Its critical/verified overlay
  denies existing parent-owned moves, requires bounded mailboxes and
  deterministic commits, denies dynamic transport, and requires frozen layout
  receipts. Resolver merging is raise-only. A focused policy spec exists;
  executable PASS still awaits an admitted self-hosted CLI.
- impl: Added an executable common parent-commit validation/order step. It
  orders envelopes by declared canonical key before checking writes and fails
  closed on malformed results, overlapping writes, and mixed reduction/normal
  updates. Snapshot application and transport remain owner/runtime work.
- impl: Added conservative `StorageLayoutRequestV1` and automatic selection.
  External ABI data stays pinned; GPU bulk-field, SIMD-block, field-separated,
  and reference AoS choices have explicit reason strings in the plan. This is
  planning only: no physical address rewriting or generic-array conversion is
  claimed until WP-22 onward.
- impl: Added `ParallelAccessPathV1` range/projection facts. Unknown ranges
  conservatively overlap; projection text alone cannot prove disjointness;
  only explicit reductions share an overlapping region without an ordinary
  conflict. This is the common fail-closed input for later borrow/MIR work.
- impl: Added boundary admission for `TransferEnvelopeV1`: owned in-memory
  regions cannot cross process, remote, or device domains; process/remote
  paths require encoded or immutable-handle payloads and device paths require
  a lease. Runtime codec/lease implementations remain pending.
- impl: Fixed the live `55.borrow` dynamic-index alias defect. Index locals
  now represent unknown runtime values and conservatively overlap; distinct
  fields and unequal constant indices remain disjoint. Added a regression
  using two different dynamic-index locals. The bootstrap-seed lint completed
  with pre-existing repository warnings and no focused source diagnostic; it
  is not self-hosted PASS evidence.
- docs: Added owner-result guidance and mirrored operational instructions for
  Codex, Claude, Gemini, and repository-agent surfaces. They explicitly mark
  contract foundations as landed and runtime transport/layout enforcement as
  pending work-package gates.
- audit: Recorded P0 runtime blocker `parallel_runtime_raw_value_transport_2026-08-12` for raw actor bits, placeholder heap copy, and unbounded RuntimeValue channel transport. It is a Rust/runtime lane and requires the planned common-contract integration plus real boundary evidence.
- plan: Added the execution-status plan with frozen interfaces, WP status,
  non-overlap assignments, immediate gates, and the admitted-self-hosted
  verification handoff requirement.
- impl: Added the canonical `TransferEnvelopeV1` byte codec. Encoding now
  admits only boundary-valid transfers, has no raw-pointer discriminant, and
  decoding rejects unknown enum values, non-boolean invalidation flags,
  reserved bytes, trailing bytes, invalid source/target pairs, and unsafe
  process-local owned-region transfers. The focused spec pins a golden owned-
  move vector, round trip, reserved-byte rejection, and process-boundary
  rejection. `git diff --check` passes. The one bounded seed lint run did not
  converge and was interrupted; the one bounded focused test run timed out at
  60 seconds amid unrelated bootstrap warnings. Neither is recorded as PASS.
  Resume command when an admitted Stage 4 CLI exists:
  `bin/simple test test/01_unit/common/structural/transfer_contract_spec.spl --mode=interpreter`.
- impl: Partially mitigated WP-13/WP-16 in the native runtime. Inline scalar
  `RuntimeValue` messages remain supported, while channel and actor paths now
  reject heap-tagged pointer payloads. Placeholder `deep_copy()` fails closed
  for mutable heap graphs instead of returning the source pointer. Focused
  native evidence passed once: actor inline/reject (1/1), channel heap reject
  (1/1), and mutable heap deep-copy reject (1/1). Full `TransferEnvelopeV1`
  runtime decoding, bounded mailbox/backpressure, graph codecs, ownership-token
  lifecycle, and separate-process evidence remain open; the P0 bug stays open.
