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

in-progress

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
- impl: Added the missing `ResolvedMemoryPolicyV1` companion. It owns only
  raise-only memory constraints—bounded buffers, address/ABI pinning, implicit
  conversion denial, and frozen receipt requirements—while leaving physical
  AoS/SoA and allocator selection to the planner/backend. Its focused leaf
  source check passed under the bootstrap seed; SDN/driver/planner consumption
  and self-hosted execution remain required.
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
- impl: Began WP-20 with a compiler-owned MIR storage-access analyzer. It
  consumes explicit ownership-region bindings and emits the existing
  `ParallelAccessPathV1` vocabulary for GEP loads/stores and field reads/writes.
  Constant single indices retain half-open ranges; dynamic, nested, unbound,
  and field projections remain conservative. Missing bindings collapse into
  one unknown region, duplicate bindings are rejected, and no backend alias or
  physical-layout claim is emitted. A fast Luna audit selected the leaf scope;
  primary review caught nested-index and ambiguous-binding soundness gaps before
  verification. The focused spec passed 4/4 through the repository wrapper;
  its orchestrator reported bootstrap-seed warnings while the test child was
  the configured pure-Simple release binary. WP-22 lowering remains open.
  The mandated compiler/lib/MCP/LSP check batch was attempted from the isolated
  worktree, then stopped under the repository runaway guard after a process
  audit found multiple unrelated 50–67 minute `check src/compiler` sessions
  already contending on the same shared compiled runtime. It is not PASS
  evidence and must be rerun by the integration owner after those stale checks
  are cleared; this lane did not terminate other sessions' processes.
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
- impl: Advanced WP-22 with a bounded, checked fixed-record storage conversion
  oracle. It validates logical schemas, type identity, non-overlapping logical
  and projected physical bytes, exact source size, and all AoS/SoA/AoSoA
  projections before copying. Exact AoS/SoA and tail-padded AoSoA round trips
  are covered, along with malformed mappings, short buffers, incompatible
  schemas, type mismatch, and the 64 MiB ceiling. A fast Luna sidecar audited
  the existing contract surface; primary review added the physical-overlap,
  type-identity, and allocation-bound defenses. This is reference evidence,
  not optimized typed-array or backend lowering, and value-semantic byte-array
  copying remains intentionally unsuitable for the production fast path.
- impl: Advanced WP-23 with a fail-closed MIR storage/SIMD admission contract.
  It admits only well-formed, non-ABI-pinned AoSoA plans whose block width
  matches the requested lanes and fits the selected fixed-width route. AoS/SoA
  select the scalar reference fallback; unsupported layouts, mismatches,
  malformed widths, and fixed-width overflow reject. SVE/RVV return an explicit
  deferred result because native scalable lowering is not landed. A Luna
  sidecar identified the existing router and backend boundary; primary review
  separated arithmetic overflow from target-width refusal and corrected the
  frozen plan-field integration. Five focused examples pass. No SIMD
  instruction, tail mask, backend lowering, or alias evidence is claimed.
  The mandated broad compiler/lib/MCP/LSP check attempt was not admissible in
  the isolated worktree: the deployed wrapper is a Rust bootstrap seed and its
  nested checks repeatedly require a missing local `bin/simple`. The focused
  module check, spec, diff check, and direct-environment guards are the current
  evidence; Stage 4 and broad parity remain open rather than being called PASS.
- impl: Extended WP-23 with a checked fixed-width AoSoA block schedule. Empty
  inputs issue no block; exact multiples contain full vector blocks; every
  partial block records a mandatory scalar tail and never a generic mask.
  Physical byte capacity, maximum block budget, required-byte overflow, and
  forged admission shapes fail closed. Fallback, rejected, and scalable
  admissions cannot produce a fixed schedule. A Luna follow-up audit confirmed
  that native backends do not share a safe masked-load/store contract; primary
  review added public-record revalidation and corrected the admission
  multiplication ceiling to signed i64. Six focused examples pass. Actual MIR
  vector instruction emission and per-backend tail lowering remain open.
- impl: Added the first executable WP-23 typed-MIR emission path. For an
  admitted full AoSoA block with already-projected input/output pointers, the
  compiler emits `MirSimdLoad`, `MirSimdBinop`, and `MirSimdStore` for the
  concrete f32/f64/i32 vector shapes already present in MIR. Tail block indexes,
  unsupported types/operations, and invalid schedules emit nothing. The API is
  currently OpenCL-only and explicitly rejects native targets before emission,
  because audit proved current x86/AArch64/RV64 selectors silently NOP these
  opcodes. Five focused MIR examples and a dedicated storage-emitted OpenCL
  source integration example pass. A diagnostic run of the broader OpenCL spec
  confirmed this new example before it was isolated, while exposing three
  unrelated pre-existing failures (Engine2D entry symbol, branch interpolation,
  atomic lowering); they are not counted as this slice's evidence. Automatic
  storage-aware loop rewriting, pointer projection, and native vector-register
  selection/encoding remain open.
- impl: Added the bounded x86 native prerequisite for WP-23. Canonical machine
  IDs now normalize consistently, AVX2 aligned f32x8 operations have distinct
  machine opcodes, and class-specific XMM/YMM allocation rejects unsupported
  widths and all spill pressure. A Luna sidecar exposed incorrect historical
  register ranges and missing high-register VEX extension handling; primary
  review therefore limited allocation to XMM0-7/YMM0-7 and made invalid SIMD
  operands fail closed. MIR-to-native selection, aligned-address proof, opcode
  dispatch, executable native bytes, high registers, and vector spills remain
  open and are not claimed by this slice.
- impl: Connected the first bounded storage-to-native x86 AVX2 route. An
  explicit `native-x86_64-avx2` request now requires a 32-byte projected-pointer
  proof before emitting aligned f32x8 MIR. Native selection assigns distinct
  low-eight YMM registers, leaves pointer values in the scalar allocator, and
  emits VMOVAPS plus Add/Sub/Mul/Div through VEX encoding that covers low/high
  GPR bases and RSP/R12 SIB addressing. Exact MIR, machine-op, register-class,
  and byte-route tests pass. Three Luna audits identified the selector,
  encoder, and test-harness gaps; primary review preserved fail-closed pressure
  and alignment rules. The current native system harness is vacuous, so real
  AVX2 host execution, CPU-feature receipts, liveness reuse/spills, and native
  end-to-end system evidence remain open rather than being called complete.
- impl: Closed the first real-host evidence gap for the custom x86 AVX2 route.
  Native SIMD selection now requires `NativeAvx2CapabilityV1`, whose canonical
  receipt key records target, evidence source/hash, admission, and reason; the
  legacy scalar entry denies AVX2 by default. A compiled-only system spec uses
  the canonical CPUID/XGETBV detector, W^X executable mappings, the actual
  MIR-to-ISel-to-regalloc-to-encoder bytes, three ABI pointer arguments, and
  eight exact IEEE-754 output checks while proving the second input unchanged.
  It passed in native mode on the current AVX2 host. Luna audits exposed the
  fake loader specs, genuine runtime detector, and correct execution oracle;
  primary review added explicit capability injection and retained honest
  skips only for absent AVX2 hardware. Production driver propagation of the
  receipt and reusable/spillable vector allocation remain open.
- impl: Propagated the resolved host AVX2 decision through the pure-Simple
  custom-native driver boundary. `SIMPLE_NATIVE_CPU` is converted to the
  existing `TargetOptContext` only when the canonical CPUID/XGETBV runtime
  probe admits AVX2; a configured cross target remains denied because a CPU
  name is not execution-domain evidence. Fixed-width SIMD modules now carry a
  deterministic `NativeAvx2CapabilityV1` from the adapter into native ISel,
  and the native cache scope includes the CPU/probe decision. Focused policy
  tests cover admitted host v3, unavailable-host denial, cross-target denial,
  and baseline/unknown denial. Three Luna audits reviewed the Simple route,
  Rust boundary, and receipt-test patterns; primary review corrected the
  initial target-vs-CPU channel mix-up. Explicit cross-target receipt import,
  public CLI admission of the custom-native backend, and vector spills remain
  open.
- impl: Removed the custom AVX2 route's false eight-destination ceiling for
  straight-line MIR. The selector computes deterministic last-use facts,
  releases dead YMM lanes before AVX three-operand destinations, and keeps
  true overlapping pressure fail-closed. More than eight sequential vector
  destinations now compile using at most three physical lanes in the focused
  fixture. Multi-block SIMD and calls are rejected because CFG liveness is not
  authoritative yet and SysV YMM state is
  caller-clobbered. Three Luna audits confirmed that generic scalar spills are
  not reusable for vectors: CFG vector liveness, one aliased XMM/YMM bank,
  32-byte aligned spill slots, def/use-aware reloads, and call handling remain
  prerequisites before vector spills can be claimed.
- impl: Advanced WP-22 from a conversion-only oracle to the first production
  host address-lowering boundary. A compiler-owned typed fixed-record view
  sidecar consumes the frozen `StorageLayoutPlanV1`, revision, element count,
  logical stride, and exact field schema, then derives overflow-checked affine
  AoS or SoA recipes for runtime indices. The custom x86 native selector lowers
  the canonical storage-address intrinsic through multiply/add machine ops.
  Focused evidence compares 64 runtime indices across unequal 1/4/8-byte fields
  with the common projector and rejects observed/ABI, unknown-field, and
  specialized-layout inputs. Luna audits identified the missing backend
  consumer and shared-oracle weakness; primary review kept ordinary RuntimeValue
  arrays untouched. Automatic `T[]` view binding/allocation, complete loads and
  stores, other backends, and executed randomized parity remain open.
- impl: Added the next WP-22 compiler boundary and a non-vacuous system oracle.
  `mir.storage.project_field.v1` rewrites only through an exact function/base
  local sidecar; missing, duplicate, dynamic-field, observed, ABI-pinned, and
  unsupported sites fail closed. Index bounds must be proven and the maximum
  affine address must fit the bound allocation capacity. The focused transform/recipe/native-selection
  unit spec passes with the temporary Rust runner (`EXIT=0`). The W^X scenario
  independently checks AoS offset 80, SoA offset 64, returned values,
  wrong-offset zeroes, and adjacent canaries. Its admitted native run is blocked
  before scenario execution by the existing
  `smf_mmap_native.spl::ptr_read_u8` codegen failure. Three bounded attempts
  were stopped; no native PASS is claimed. Driver registration and public typed
  view allocation remain open.
- impl: Connected WP-22 bindings to the production native driver boundary.
  `CompileContext` owns module-qualified aligned rows, rejects duplicate sites,
  evicts rows with MIR, and generates registration-order-independent complete
  sidecar identity for the native cache scope. The backend helper optimizes
  first, atomically rewrites a fresh module, then admits only custom-native
  x86_64 pointer-width fields. Canonical MIR cannot be partially rewritten on
  failure. Large base offsets use an i64 register beyond signed `ADD_IMM` range.
  Focused storage and registry specs pass (`11` and `3` assertions/groups via
  the bounded Rust-runner diagnostic lane). Public typed-view allocation and
  producer registration, formal receipts, subword fields, other backends, and
  the blocked W^X scenario remain open.
- impl: Removed the loader blocker beneath the W^X layout scenario. The old
  `native_mmap_read_bytes -> slice_from_raw_parts -> *u8` path was both
  unsupported by MIR lowering and copied each byte twice. Canonical
  `rt_ptr_read_u8` now exists in runtime C, Rust SFFI, interpreter dispatch,
  codegen signatures, and the runtime-symbol registry; the Simple loader copies
  once through exact-width reads. Rust exact-byte tests cover 0x00/0x7f/0x80/
  0xff/0x5a and argument rejection, and a Simple adjacent spec covers ranges,
  invalid inputs, and strings. A native runner briefly reported green only by
  fabricating unresolved assertion/helper stubs; that result was rejected.
  A clean bounded `cargo check -p simple-compiler -p simple-runtime` now passes.
  The focused Rust test build reached compilation but hit its 90-second cap
  before executing, so re-admission still requires a fresh runtime artifact and
  a non-stub W^X execution.
- impl: Froze the missing compiler-owned typed-view declaration authority for
  the next WP-22 producer tranche. A declaration binds one final MIR
  function/base local to an exact compiler-owned raw allocation provenance,
  source revision, fixed capacity/schema, AoS/SoA plan, and bounds proof.
  Admission validates every field recipe and currently requires 8-byte scalar
  fields. RuntimeValue arrays, external/pinned storage, address-observed data,
  missing bounds, undersized allocations, and unsupported layouts fail closed.
  The focused spec passes 3/3. Automatic source-pattern production and
  registration of the provenance/revision evidence remain open.
- impl: Added the automatic canonical-MIR producer for
  admitted compiler-owned views. It requires a same-block owned-raw allocation
  marker and independently proves a constant index is within the declared
  element count before replacing `GEP -> Load(record) -> GetField` with
  `PROJECT_FIELD(address) -> Load(value)`. Temporary escapes, stale/duplicate
  declarations, missing markers, and out-of-range indices fail atomically.
  Producer evidence retains allocation provenance, source revision, contract
  version, and pattern identity. Backend projection now resolves site LocalIds
  before generic optimization, then optimizes backend-ready address MIR.
  The focused producer spec passes 4/4 and the adjacent native projection suite
  passes 11/11. The production helper accepts declarations, runs the producer
  atomically, resolves logical sites before generic optimization, and then
  compiles backend-ready address MIR.
- impl: Added the authoritative MIR allocation owner for compiler-private typed
  raw views. `MirBuilder.emit_typed_storage_alloc_owned_raw_v1` emits one exact
  raw-allocation intrinsic and returns an immutable allocation fact containing
  final base LocalId, bytes, logical type, numeric/source revisions, count,
  stable compiler-site provenance, and allocation identity. MIR-opt converts
  that fact into a declaration without a layer inversion. The producer requires
  the same allocation identity, consumes the owner intrinsic, and materializes
  `rt_alloc` before codegen. Focused owner/declaration/producer suites pass
  1/1, 4/4, and 4/4. No existing RuntimeValue, mmap, linker, or ABI-pinned
  allocation is relabeled. Driver full-evidence registration/freeze remains.
- impl: Added the driver-owned full-evidence registry and install transaction.
  CompileContext now batch-preflights aligned site/evidence rows, retains
  allocation identity/provenance/source revision, producer version/pattern,
  bounds-proof kind, and projection count, atomically installs rewritten MIR,
  and rejects partial/duplicate/legacy rows. One-way freeze captures a sorted
  immutable identity before native cache scope creation; registration after
  freeze is denied and MIR eviction cannot mutate frozen receipt authority.
  Registry + producer suites pass 7/7 and 4/4. A real compiler pilot still
  needs to call the allocation owner and install transaction before freeze.
- impl: Added the contained compiler-private WP-22 compile-chain pilot
  (`driver_typed_storage_pilot.spl`) and its integration fixture. The pilot
  uses the real MIR allocation owner, derives its declaration from the returned
  allocation fact, emits `rt_free`, invokes
  the automatic producer, and routes the result through CompileContext install,
  freeze, and custom-native compilation. It is not public `T[]` support.
  The focused integration gate passes 3/3 in interpreter mode. Static review
  found and removed a physical initialization GEP (slot 8/10) that had been
  checked as a logical element index against count 5; the fixture also avoids a nested
  module/producer-result wrapper, uses scalar AoS/SoA leaf installers to avoid
  known Stage4 enum transport hazards, and guards evidence indexing. A new
  companion system fixture derives affine constants from the installed/frozen/
  lowered module and executes them through W^X. Its first run was rejected for
  missing coverage metadata, its native-mode retry could not find a worktree-local
  `bin/simple`, and its interpreter-mode scenario failed without exposing the
  assertion. The three-cycle cap stopped further retries. Therefore executable
  derived-constant and installed-function allocation/free lifetime evidence
  remain open; no W^X PASS is claimed.
- impl: Strengthened WP-20 logical access facts at the production typed-storage
  boundary. Constant element ranges now survive `GEP -> Load(record) ->
  GetField`, retaining paths such as `index:2.field:4` without treating fields
  themselves as disjoint. A flat summary conservatively derives address escape
  and unknown access through stores, casts, aggregates, returns, indirect
  calls, and unknown direct calls; only exact `rt_free(bound_base)` finalization
  is admitted. The typed-storage producer rejects observed or unclassified
  owner regions before rewriting. Focused analysis and producer suites pass
  6/6 and 5/5. These facts emit no alias metadata or scheduling permission;
  completeness-tracked layout advisory and planner integration remain open.
- impl: Added the bounded WP-20-to-WP-21 typed layout advisory bridge. Public
  access paths deliberately retain conservative record-load and field facts;
  a separate def/use-derived terminal-event view excludes a record Load from
  planner counts only when every use is a direct field projection. Unknown,
  dynamic, address-observed, whole-record, co-accessed, empty, and non-sparse
  evidence keeps the reference layout. Complete sparse field evidence may set
  the existing planner's locality hint, while ABI, GPU, and SIMD inputs remain
  explicit and no alias/scheduling authority is emitted. Advisory, access, and
  producer gates pass 4/4, 6/6, and 5/5.
- impl: Connected `ResolvedMemoryPolicyV1` to that advisory as a fail-closed
  compiler adapter. Address-observed policy pins produce `ExternalFixed`; a
  conversion-denying profile suppresses automatic SoA/SIMD/GPU choices, and a
  SHA-256 of the base policy plus memory policy participates in the selected
  layout identity. The bootstrap leaf check passed. Driver/SDN policy loading,
  planner invocation from a real allocation owner, and self-hosted execution
  remain open.
- audit: WP-30 remains intentionally unimplemented. The current `85.mdsoc`
  codegen/optimization/module-loading ports are descriptive counters without
  a driver stage call chain carrying transfer/layout/commit policy. Adding a
  parallel port there would be paper-only and could not satisfy the required
  bypass probe. The next real integration owner is the production process
  spawn/piped adapter, after it can hand a bounded frame to the parent ingress
  and retain cancellation/cleanup evidence.
- impl: Hardened the WP-22 native handoff boundary. Registry freeze now
  deep-copies field rows and full evidence, validates site/evidence equality,
  records the complete module universe including zero-site modules, and uses
  length-prefixed text components for stable cache/module identity. Storage-
  bearing modules are kept on the owner compilation thread because the current
  ParallelBuilder closure still captures mutable CompileContext and no frozen
  MIR+storage capsule exists. Bootstrap-local routes reject typed-storage rows
  instead of bypassing lowering. The focused registry gate passes 11/11 and
  the bootstrap leaf check passes; the large AOT leaf/check and changed-file
  lint exceed the current pure checker 180-second watchdog, so full Stage4
  worker-capsule and compiler-wide verification remain open.
- impl: Added the compiler-owner MIR+storage capsule boundary. After cache-hit
  classification, the parent resolves bootstrap/dictionary MIR once, pairs it
  with the frozen module storage snapshot and immutable compile scalars, and
  creates class-handle capsules for every uncached module. The builder callback
  accepts only the frozen batch and module name: it has no CompileContext or
  BuildCache access. Codegen revalidates complete MIR metadata and storage
  evidence before and after compilation; the result receipt binds capsule,
  object path, byte size, and content hash. A parent-only collector validates
  each receipt and checkpoints the cache per successful unit. The 16/16 focused gate proves capture
  survives live MIR/registry replacement and routes four mixed storage/zero-
  site capsules through the non-deterministic builder branch. This is branch
  transport parity, not actual concurrency: `ParallelBuilder.build` still
  invokes callbacks sequentially, while process workers require a complete MIR
  codec rather than in-memory class pointers.
- impl: Began WP-18 with a bounded runtime-owned scalar task domain rather than
  copied mutable `ThreadPool` values. Capacity covers each accepted unreleased
  task; release restores credit and frees the task record. State/task handles
  use disjoint tagged generation domains and lifetime pins, so stale, forged,
  wrong-kind, release/destroy races reject instead of dereferencing process
  pointers. The internal entry contract accepts a compiler-produced,
  noncapturing direct-function descriptor with InlineCopy input/result and
  copies that descriptor into the task record. Both shipped C providers and
  compiler symbol routes are aligned; the common capacity limit is 65,534.
  Rust gates cover bounded credit, independent states, 100k reuse,
  stale/cross-kind rejection, and a destroy-vs-metric pin race. The native
  descriptor path now normalizes tagged Simple function values before
  validating and copying the direct-function record. The attempted native
  Simple facade gate
  `test/03_system/feature/usage/pool_state_i64_native_spec.spl --mode=native`
  reached the runner daemon but timed out without an assertion verdict; its
  uncommitted facade/spec are therefore not release evidence. Resume with one
  bounded self-hosted native run that reaches the scalar callback, Full until
  release, close/idle, and destroy checks. Public Simple exposure,
  alternate-provider execution, legacy ThreadPool globals,
  cancellation, blocking backpressure, and heap transfer remain open.
- impl: Tightened the reachable WP-14 actor mailbox admission contract.
  `ActorMailbox.new(0)` and negative capacities now resolve to the finite
  policy default of 256 rather than creating an unbounded queue; explicit
  positive capacities remain configurable. The mailbox now uses a bounded head
  cursor and compacts only when full backing storage is reused, avoiding an
  array front-slice on every dequeue. The new pure capacity-resolution unit
  fixture is retained, but the available bootstrap runner/check path emits
  dependency warnings without a final verdict; it is not counted as behavioral
  evidence. A real self-hosted native FIFO/compaction/backpressure execution
  gate remains required.
- impl: Began the WP-16 actor ownership repair. `ActorMailbox` is now a
  copyable handle around one `ActorMailboxState` class, so an `ActorRef` and
  scheduler-held `Actor` copy address the same bounded queue rather than two
  independent value queues. This is not yet an admitted actor transport:
  scheduler/global lifecycle values remain legacy, and native send/ask routing
  plus close/cancellation behavior need execution evidence.
- impl: Tightened the WP-15 parent commit ordering path. The bounded
  65,535-result admission limit previously fed a quadratic repeated-selection
  sort; ordering now uses stable bottom-up merge passes, preserving left-run
  order for equal keys and reducing ordering work to O(n log n) with bounded
  temporary arrays. A reverse-completion 16-result regression is present.
  The available source-check wrapper timed out without a final verdict; resume
  with `bin/simple test test/01_unit/common/structural/parallel_commit_contract_spec.spl --mode=interpreter`
  on an admitted self-hosted CLI before treating the regression as execution
  evidence.
- impl: Added `ParentCommitOwnerV1` as the runtime-owned serialized parent
  root for local applications. It holds only the current revision/snapshot
  token behind one mutex, delegates batch validation/order to the frozen common
  engine, publishes a new root only on a valid receipt, and leaves stale or
  conflicting batches unchanged. Its native-focused spec reached bootstrap-seed
  runner diagnostics without a verdict. Resume once with
  `bin/simple test test/01_unit/lib/nogc_async_mut/parent_commit_owner_spec.spl --mode=native`
  using an admitted self-hosted CLI; child transport, payload apply/verify,
  cancellation, and process-level commit remain open.
- impl: Connected that owner to the frozen transfer contract through
  `ParentCommitSubmissionV1`. `commit_submissions` requires a boundary-valid,
  non-parent source whose destination is the parent before the common
  deterministic commit transition runs; parent-originated and wrong-domain
  submissions return a diagnostic receipt without replacing the root. This
  is contract/runtime wiring only until a real child actor/process delivers
  one submission through the native transport path.
- impl: Added the bounded `SPRS` ResultEnvelopeV1 payload codec and connected
  it to the Process-to-Parent owner boundary. The frame codec first validates
  its process route/checksum, then the result codec validates a versioned,
  UTF-8, pointer-free result before the existing transfer-gated submission
  path may publish it. A pinned wire vector and malformed kind/reserved-byte
  checks cover the codec contract. The bootstrap-only source check did not
  produce a final verdict and the prior interpreter SSpec output was
  truncated, so this remains contract wiring—not evidence of a child process
  executing or delivering an accepted result.
- impl: Added `ParentCommitFrameInboxV1`, a mutex-owned bounded FIFO for
  Process-to-Parent result frames. Admission validates both existing frame
  transport and the typed result codec before retaining an independent byte
  copy; a head cursor avoids front-slice churn, close drains accepted frames,
  and a full inbox returns backpressure. The parent drains one frame through
  `ParentCommitOwnerV1`, preserving permanent consumption on stale/conflict
  rather than silently retrying. The bootstrap source check passed; the
  focused interpreter SSpec produced truncated bootstrap output without a
  final verdict, so real IPC and native backpressure execution remain open.
- impl: Extended the parent owner to decode and commit a bounded batch of
  accepted Process-to-Parent frames in one common-engine transition. Every
  frame must pass route, checksum, and typed-result validation before the
  owner calls `commit_submissions`; one malformed frame leaves the root
  unchanged. Reverse-arrival coverage pins task-id canonicalization, but the
  changed focused SSpec has not yet obtained a self-hosted verdict.
- impl: Composed that inbox and batch transition through
  `drain_process_result_batch`. The parent chooses a per-drain budget without
  overriding queue capacity, receives only already accepted frames, stops at
  empty/closed, and publishes the drained set in one atomic transition. Empty,
  broken-lock, and non-positive-budget paths remain diagnostic/no-publish.
- impl: Added an independent retained-byte ceiling to the process ingress
  queue. Admission now requires both a frame slot and sufficient byte budget;
  dequeue subtracts the exact copied frame length before reuse. The default
  byte ceiling is 16 MiB and callers that need a tighter bound can pass an
  explicit positive budget. This prevents a small frame-count capacity from
  becoming an implicit multi-megabyte-per-frame growth policy.
- impl: Added parent-ingress high-water and admission counters under the same
  mutex as its queue state. Tests can now assert bounded accepted/rejected
  frames, retained bytes, and peak occupancy deterministically without using
  host RSS as the primary oracle. Native multi-process pressure evidence is
  still required before treating these counters as an end-to-end result.
- impl: Added `SPRF1` canonical lowercase-hex armor and
  `ParentCommitPipedResultReaderV1` over the existing native text-pipe
  surface. The reader reassembles split stdout writes, obeys a parent line
  budget, and sends only route/checksum/schema-verified frames into the
  bounded inbox; malformed and oversized text is rejected without becoming
  retained binary input. Focused bootstrap-seed syntax checking passed, while
  focused interpreter invocations produced truncated output with no final
  verdict. Self-hosted native child launch, pipe backpressure, cancellation,
  and cleanup evidence remain required.
- test: Added the native-only system gate
  `test/03_system/feature/language/parent_commit_piped_result_spec.spl`.
  It launches `/bin/echo` through the canonical piped-process facade, polls
  actual stdout into the new reader, then commits the decoded child result.
  Its interpreter capability probe skips only the known seed extern gap;
  no self-hosted native verdict has been obtained in this environment.
- verify-blocked: The one available deployed self-hosted launcher was invoked
  for that exact native gate on 2026-08-13. `bin/release/simple` rejected the
  run before test discovery because its bounded ABI probe executes
  `release/x86_64-unknown-linux-gnu/simple test --help`; that binary
  segfaulted (exit 139). Its `--version` succeeds and identifies
  `Simple v1.0.0-beta`, so this is a concrete deployed test-command crash,
  not evidence that the process result test passed or failed. Resume only
  after repairing the self-hosted `test --help` crash, then run once:
  `SIMPLE_LIB=src bin/release/simple test test/03_system/feature/language/parent_commit_piped_result_spec.spl --mode=native`.
  The established root-cause record is
  `doc/08_tracking/bug/native_selfhosted_run_segfault_startup_normalize_2026-07-24.md`:
  the source guard is landed, while fresh deployment is blocked by the
  stage-4 parse-memory balloon. This lane must not duplicate that compiler fix.
- impl: Added a parent-reader retained-partial-line high-water counter. The
  line reassembler records the maximum text it owns across split writes and
  deferred scheduling, while oversized input is discarded rather than raised
  into that metric. The focused leaf check was attempted once with the deployed
  self-hosted binary and also segfaulted before a verdict, so this is a
  source-reviewed metric plus focused contract fixture, not native execution
  evidence.
- impl: Reader close is now terminal for retention as well as frame admission.
  It clears a partial armored line and rejects subsequent chunks before they
  can be appended, closing the prior closed-inbox-but-retained-text gap.
- impl: The armored stdout reader now rejects non-ASCII text before buffering
  it. This makes its advertised line ceiling a real retained-byte bound rather
  than a character-count approximation over the host `text` surface.
- impl: Actor mailbox read-side observations now use the shared mailbox mutex
  instead of racing queue/head fields with enqueue or dequeue. A retained
  message high-water counter records bounded occupancy across copies; it does
  not upgrade the legacy actor route into typed native transport evidence.
- impl: The single-threaded actor scheduler now consumes ready IDs through a
  cursor and compacts only a half-consumed large prefix. Requeue deduplication
  scans the active suffix, preserving round-robin semantics without one
  front-slice allocation/copy per dispatch.
- impl: Legacy actor asks now reserve a bounded reply slot at admission. The
  reservation remains occupied through completion until consume/cancel; enqueue
  failure, handler error, and scheduler actor-unregister release it. This
  prevents unconsumed completed replies from growing without bound and rejects
  new asks rather than silently dropping outcomes. Native lifecycle evidence,
  typed payload transfer, and actor-stop outside the scheduler remain open.
- impl: `ActorScheduler` is now a class-backed authority rather than a copied
  value struct. Global actor references therefore mutate the same scheduler
  registry, ready queue, reply reservations, and counters; this closes the
  scheduler half of the prior copied-handle split.
- impl: `ActorRef` now retains its admitting `ActorScheduler` authority. This
  makes `spawn_on(custom_scheduler, ...)` route send, ask, synchronous ask, and
  bounded reply cancellation through that custom scheduler instead of the
  ambient global scheduler. It is a single-threaded routing repair; native
  actor lifecycle evidence and typed transfer remain open.
- impl: `ActorRef.stop()` now delegates to that same scheduler. Scheduler-owned
  stop drains queued asks, cancels their bounded reply reservations, removes
  ready work, and reports a wrong-scheduler/unknown-actor stop as false.
- impl: Removed the priority mailbox's capacity-zero unbounded admission mode.
  Compatibility `unbounded()` now selects the finite default, and the queue
  owner normalizes forged/non-positive configurations before it accepts work.
- impl: Priority-mailbox selective receive now decrements retained-byte
  accounting on every queue branch, matching ordinary receive and stale-drop.
- impl: Priority-mailbox lifecycle counters now classify selective delivery as
  processed and stale eviction as dropped, keeping bounded-memory telemetry
  consistent with the queue's actual ownership transitions.
- impl: Priority-mailbox high-priority occupancy now releases on delivery,
  selective removal, stale eviction, and clear, so reserve telemetry cannot
  retain phantom high-priority pressure.
- impl: Priority reserve now applies only when priority admission is enabled.
  Default normal-only mailboxes retain their full finite capacity rather than
  silently withholding an unusable high-priority reserve.
- impl: `Actor` is now class-backed too, preserving its lifecycle, dispatch,
  and error fields through scheduler registry iteration. Mailbox sharing alone
  was insufficient because the surrounding actor values still lost those
  updates when copied.
- impl: Made bounded actor send admission observable: `ActorRef.send` now
  returns the mailbox acceptance result and queues scheduler work only after
  a message is admitted. The shared pure predicate rejects malformed counters
  and non-positive capacities rather than reintroducing an unbounded sentinel.
  One focused interpreter invocation reached bootstrap-seed diagnostics without
  a final verdict, so native actor send/ask routing remains an explicit gate.
- impl: Added shared mailbox closure: `Actor.stop` closes its class-backed
  mailbox before discarding queued work, and all copied handles thereafter
  reject new sends while any already accepted work can still drain. A focused
  close/copy fixture exists. The bootstrap-only mailbox check did not emit a
  final verdict, so native close wakeup, scheduler interaction, and actor
  lifecycle execution remain open.
- impl: Reworked the generic scalar `BoundedChannel` receive path to use a
  consumed-prefix cursor. It now compacts only when a later append needs the
  bounded backing storage, rather than calling front removal on every receive.
  The focused bootstrap source check passed; this is a storage-cost repair,
  not evidence of a thread-safe task mailbox or typed transfer transport.
- impl: Reworked `ThreadSafeQueue` removal to use a consumed-prefix cursor.
  It compacts amortized storage under its mutex rather than slicing the full
  remaining task-ID queue on each pop; admission and sentinel semantics are
  intentionally unchanged pending the separate bounded typed-envelope rewrite.
- impl: Reworked `HostJoinSet` completion delivery to use a consumed-prefix
  cursor. Completed result order remains FIFO while streaming joins no longer
  copy the remaining completion queue per result.
- impl: Reworked `HostScheduler` global FIFO dequeue to use a consumed-prefix
  cursor. Normal-priority scheduling is amortized O(1); critical-priority
  prepend compacts only the live suffix to preserve its existing precedence.
- impl: Reworked the legacy cooperative `Executor` ready queue to use a
  consumed-prefix cursor. Ready-task ordering is unchanged while completed
  dequeues avoid copying the remaining ready IDs on every iteration.
- impl: Reworked mimalloc page free-list allocation to pop its appended tail.
  Local and raw frees already append, so LIFO reuse avoids copying remaining
  free-list entries while preserving page ownership and capacity accounting.
  The tail pop is direct (not a tail slice), so the cost claim is exact.
- impl: `Runtime.block_on` now consumes its completed result before returning.
  This prevents the global convenience runtime from retaining one completed
  entry per blocking call; detached `spawn` result retention remains a
  separate bounded join/result-contract task.
- blocker: Legacy `Runtime.spawn` has no admitted join/take/cancel result
  lifecycle, so detached completed entries remain unbounded. Tracked as
  `async_runtime_detached_completed_results_unbounded_2026-08-13.md`; do not
  add silent eviction before WP-14/WP-18 supplies explicit terminal outcomes.
- doc: `parallel_apps.md` now explicitly excludes the separate `std.actors`
  legacy runtime from the bounded `std.actor` contract. Its copied mailbox,
  drop-oldest overflow, and unbounded reply store require migration rather
  than compatibility claims.
