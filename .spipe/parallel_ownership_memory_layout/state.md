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
- impl: Extended WP-02 with a storage-specific, overflow-safe projection
  contract for AoS, SoA, AoSoA, and pinned external layouts. Bounds, field
  extent, power-of-two alignment, ABI conversion, and block-stride violations
  now fail closed. Grouped/tiled/packed/factored mapping and canonical wire/hash
  vectors remain explicit follow-up work. Seven focused examples exit zero via
  the available Rust bootstrap seed; this is not self-host authority evidence.
- impl: Completed the frozen WP-02 V1 identity layer without changing its
  record shape: canonical `SPSL` bytes, exact checked decoding, explicit
  field-wise equality, and SHA-256 over canonical bytes now have a pinned
  golden vector. Unknown enums, bad envelopes, reserved bytes, trailing bytes,
  and invalid UTF-8 fail closed. Additional research fields require a ratified
  V2; specialized grouped/tiled/packed/factored projection remains separate.
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
- impl: Added the native `SPTR` v1 envelope and inline packet implementation.
  The 40-byte metadata matches the Simple golden vector; actors now exchange
  exact 48-byte validated packets, heap actor construction context is rejected,
  and the native compatibility channel stores packets in a finite 256-item
  queue with full reported as send failure. Focused evidence passed once: two
  transfer codec tests, actor packet round trip, heap-context rejection, and all
  nine channel tests, and bounded actor backpressure. Actor inbox/outbox queues
  are also finite at 256 and actor reply provenance is `Actor -> Parent`.
  Compilation used a temporary isolated-worktree removal of
  the unrelated missing `rt_io_tcp_probe_peer` re-export and restored it after
  testing. Full graph codecs, policy-selected mailbox capacities, ownership-token
  lifecycle, process transport, cancellation, and self-hosted evidence remain.
- runtime decision: `runtime_need` = native safe boundaries delegated below the
  Pure Simple common contract still lacked a byte-compatible packet and finite
  channel storage; `facade_checked` = common `TransferEnvelopeV1` codec and
  existing `std.concurrent.channel`; `chosen_path` = runtime-owned change with
  no new public `rt_*` entrypoint; `rejected_shortcuts` = raw pointer bits,
  unclassified `Any`, unbounded replacement queue, fixture-only bypass, and
  pretending inline-only packets implement graph ownership transfer.
- impl: Hardened the WP-13/WP-16 native compatibility channel lifetime. The
  heap handle now owns one ref-counted channel state; every public operation
  clones that state while the heap-allocation registry lock still proves the
  handle live. Close is atomic, sender teardown is serialized, and free uses
  checked unregister so concurrent or repeated frees fail closed. Focused
  native evidence passed once: all 11 channel tests, including acquired-state
  survival after handle free and concurrent send/close/free. This does not yet
  add graph codecs, typed public endpoints, policy-selected capacity, or
  ownership-token payload transfer.
- impl: Added the reviewed WP-13 bounded leaf `EncodedCopy` codec in the native
  runtime. Lossless boxed `f64`, boxed `u64`, and immutable UTF-8 strings are
  copied by logical content under registry protection and materialize as new
  heap identities; arrays, dictionaries, tuples, forged pointers, device, and
  unauthenticated remote routes fail closed. The deterministic wire includes
  the `SPTR` envelope, leaf kind, exact length, reserved bytes, a corruption
  checksum, and a 1 MiB ceiling. A fast Luna sidecar scoped the audit; the
  primary high-capability review caught and closed remote/device admission
  before merge. All seven focused transfer tests passed once after review.
  Graph/schema codecs and production actor/channel/process integration remain.
- impl: Advanced WP-17 with `process_transfer.rs`: an encoded-copy-only process
  frame reuses the 40-byte `SPTR` metadata, enforces the destination domain,
  carries an exact length and corruption checksum, and caps codec payloads at
  4 MiB. PID-namespaced region IDs prevent counter collisions for one live
  same-host parent/child pair; they are not global identity across PID
  namespaces, PID reuse, or replay. One
  focused test launches a real child test process to decode parent input and
  return a child-created result; a second test rejects wrong
  targets, corruption, and oversize. Both passed once. Current `main` has no
  `rt_pg_parallel_worker_handoff_*` implementation, so the stale plan wording
  was corrected instead of recreating an aggregate-pointer handoff. Production
  spawn/piped integration, schema/ObjectRef codecs, cancellation rollback, and
  self-hosted evidence remain open.
- runtime decision: `runtime_need` = a process destination cannot admit the
  inline RuntimeValue packet used by thread/actor boundaries;
  `facade_checked` = common `TransferEnvelopeV1`, native transfer codec,
  `native_spawn_worker`, and the C piped process surface; `chosen_path` =
  `runtime-owned-change` adding bounded internal framing without a new public
  `rt_*` symbol; `rejected_shortcuts` = inherited heap pointers, raw
  RuntimeValue bits, the removed aggregate PG-worker handoff, unbounded bytes,
  and calling a focused fork test production integration.
- impl: Added the missing common/native WP-17 frame agreement. Pure Simple now
  encodes and decodes the exact native 56-byte process header plus bounded
  payload, using the same Parent/Process route checks, 4 MiB cap, and FNV-1a
  corruption checksum. Both runtimes pin the same complete-frame golden vector;
  Simple also rejects wrong target, corruption, trailing bytes, and oversize.
  FNV is corruption detection, not authentication. Production spawn/piped
  integration and parent-issued session/generation replay checks remain open.
- impl: Advanced WP-15 with a memory-bounded functional owner transition.
  `ParallelCommitStateV1` retains only `(revision, snapshot_token)` rather than
  an unbounded envelope history. The engine validates the complete batch before
  one proposed root assignment; stale bases, conflicts, duplicate task/sequence identity,
  duplicate in-batch payload tokens, malformed state, and invalid candidate
  roots leave the original state unchanged. Successful non-empty batches
  advance exactly one revision and receipt canonical task/sequence/payload
  order, and receipt shape is validated. Nine focused examples pass, including three completion permutations,
  stale mixed input, conflict, duplicate identity, and successful publication.
  The available binary explicitly identifies as a Rust bootstrap seed, so this
  is focused development evidence, not admitted Stage 4 acceptance. Payload
  apply/verify, mutation-receipt adaptation, receipt hashing/wire format,
  access-range/fixed-tree integration, candidate capability checks, and a
  serialized/CAS runtime/MDSOC owner adapter remain open; this common value
  function is not itself concurrent atomic publication.
- impl: Advanced WP-03 receipt integrity with a bounded canonical `SPCR` wire
  identity, exact checked decoding, field/array equality, SHA-256 identity, and
  a hand-pinned golden vector. Receipt validation now rejects invalid ordered
  IDs/sequences/tokens, oversized batches, revision overflow, and reductions
  used without the explicit reduce policy. Malformed owner states produce a
  valid diagnostic receipt. This hash attests receipt/order identity only: it
  does not attest payload contents, candidate-root lineage, or concurrent
  atomic publication; those still require the runtime owner adapter and V2
  root/payload evidence.
- impl: Advanced WP-10 by unifying MIR fact emission and NLL checking on one
  global program-point layout. CFG construction now records terminator points,
  derives successor/predecessor edges, and reaches non-entry blocks. Borrow
  propagation uses block entry/terminator points rather than conflating block
  IDs with fact points, and borrow IDs are function-global so predecessor facts
  cannot overwrite each other at joins. A two-block adversarial MIR test now
  detects shared/mutable conflict in the successor. Path-sensitive moved-state
  joins, loop fixed points, borrow liveness termination, and range proofs remain
  open; backend `noalias` still must not rely on this checker as fully authoritative.
- impl: Advanced WP-11 with a compiler-owned HIR boundary classifier for
  inline copies, frozen shares, isolated moves, runtime-classified aggregates,
  and rejected borrows/raw pointers/mutable class graphs. Existing parent-owned
  `iso` input produces `W-PAR-OWN-001` under the balanced policy and
  `E-PAR-OWN-001` under critical assurance; process/remote pointers produce
  `E-PAR-PROC-003`. The driver derives the parallel policy from its resolved
  assurance strictness. Eight focused HIR examples pass once. This is partial:
  the active seed still lowers source `spawn(...)` incorrectly, method/task/
  actor/process capture surfaces are incomplete, explicit source `move` is not
  yet preserved at this HIR call site; the following WP-12 slice begins that
  MIR work without claiming runtime transport completion.
- impl: Advanced WP-12 with explicit MIR `TransferOut`, `TransferIn`,
  `FreezeRegion`, `AcquireSnapshot`, and `CommitUpdates` operations plus stable
  JSON text, optimizer/visitor use/definition facts, GC-copy facts, and
  borrow-checker ownership facts. MIR keeps WP-01's mode and payload as
  separate enums and marks unresolved dynamic classification explicitly.
  `TransferOut` produces a distinct transport local so an owned move consumes
  the source exactly once while the following transport call reads the
  envelope local. Both the dormant structured Spawn/Send lowering and the
  currently reachable literal `spawn`/`spawn_actor` ordinary-call path emit
  transfer facts; isolated arguments use owned-move and unclassified values
  remain runtime-classified. The final `bin/simple check src/compiler` reached
  no errors. The focused five-example spec
  compiled past that correction but the current broad `SIMPLE_LIB=src` runner
  exited during dependency loading without a verdict on three capped attempts.
  Runtime/backend transfer-envelope lowering, process/device domains, incoming
  receive emission, and real source-to-MIR execution evidence remain open; no
  backend alias claim may rely on this partial slice.
- impl: Advanced WP-13 with fail-closed native RuntimeValue classification and
  an opaque ownership-region authority state machine. Inline values are the
  only bit-copy class; forged heap tags are distinguished from registered heap
  graphs, mutable graphs require a codec, synchronized handles require their
  own handle envelope, and device/remote inputs are unsupported rather than
  copied. The state machine admits only regions already proven sealed, records
  `Local -> InTransit -> Local(generation+1)`, rejects a second move and wrong
  receiver, and rolls transport failure back to the source with a new
  generation. It transports no pointer or RuntimeValue payload and therefore
  does not claim arbitrary graph isolation. Seven focused Rust tests pass
  (3 ownership, 4 transfer). Graph sealing/materialization, global/session-safe
  registry identity, typed handle transport, and actor/channel/process wiring
  remain open.
- impl: Closed the native isolated-thread NIL-substitution hole. A new
  `clone_for_isolated_thread() -> Option<RuntimeValue>` distinguishes valid NIL
  from rejected input, copies inline values, admits only registered channel
  handles as synchronized sharing, and rejects every other heap graph. All four
  Rust spawn variants (ordinary/limited, one/two inputs) validate every input
  before allocating a thread ID or creating an OS thread; the formerly raw
  second argument is no longer an arbitrary heap-pointer bypass. Five focused
  regressions pass (single input, second input, limited equivalents, channel
  handle). A broader `isolated_thread` filter also exposed two pre-existing
  scalar worker ABI heuristic flakes (`raw_worker_args`, results 5/36 instead
  of 42); these are not treated as evidence against the new exact tests. The C
  `runtime_thread.c` lane still passes raw two-argument payloads and cannot yet
  distinguish synchronized heap handles, so cross-runtime parity remains open.
