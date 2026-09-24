# L7 three-payload bounded formal model and source replay

**Status:** authored, not admitted  
**Current receipt:** `NotChecked`; individual model roots may become
`ModelProven` only after their Lean/axiom gate passes  
**Source refinement:** OPEN

The [2026-09-11 source audit](#2026-09-11-three-file-and-invalidation-audit)
below distinguishes the eligible three-file profile from ordinary compilation
and specifies stronger, still-unproved invalidation/publication obligations.

## Scope

This additive verification capsule covers a deliberately bounded part of the
three-payload compiler/cache path:

- B01: a broker model in which every attempted role is a prefix of source,
  optional prior TLD, and effective initializer TLD; successful traces contain
  exactly two cold or three warm role reads; charged successful bytes do not
  exceed the caller budget.
- B02: current source replay binds the prepared closure to the exact source
  bytes and rejects a mutated source snapshot. It also exercises the existing
  semantic binder and resolver while their typed body authority remains
  unavailable.
- R01: full-record reverse-reference replacement reconstructs membership and
  preserves an unrelated consumer. Current source replay checks fingerprint
  and manifest replacement plus consumer mismatch rejection.
- Publication model: exact record replay is idempotent, a conflicting prefix is
  rejected, and a protected model pin is never classified eligible for sweep.
- Source identity: changing the source-byte hash makes a binding stale.

The model does not prove compiler semantic equivalence, failed-read physical
instrumentation, live writer or reader authority, host durability, crash
atomicity, transitive CAS closure, database publication, filesystem races,
native output, startup time, or RSS.

## Assurance separation

`lake build` checks only the Lean model. A matching bounded Simple replay binds
selected current functions and bytes to observations. Neither fact alone, nor
their hashes, promotes the result to `SourceRefined`. This stage intentionally
defines no promotion function and changes no availability gate.

The required formal receipt is fail closed. Its DTO observations are not
unforgeable execution receipts, so this stage always emits `NotChecked`, counts
zero killed mutants, and cannot issue `ModelProven`. A later owner-backed
extension must bind the exact fixture set, runner identity, individual mutant
identities/results, current source-binding equality, and complete closed axiom
audit before `ModelProven` is possible. Missing executable mutation evidence
leaves the mutation gate OPEN.

## Proof capsule

The project is
`src/verification/three_payload_compile`, uses Lean `v4.30.0`, imports every
proof module through `ThreePayloadCompile.Audit`, and prints the transitive
axioms of every mandatory root.

| Root | Model claim | Source replay | Refinement boundary | Current evidence |
|---|---|---|---|---|
| `ThreePayloadCompile.broker_prefix_read_bound` | Any trace length is at most cold 2 / warm 3 | cold/warm physical broker fixtures | failed-read instrumentation and facade contract OPEN | authored; Lean gate not admitted |
| `ThreePayloadCompile.broker_success_read_count` | success has exactly cold 2 / warm 3 roles | `broker_cold2`, `broker_warm3` | facade calls are not OS syscall counts | authored; replay unavailable |
| `ThreePayloadCompile.broker_prefix_byte_bound` | charged successful bytes are within the budget | physical receipt bytes equal the prepared payload | a foreign facade returning more than requested is TCB/unrefined | authored; replay unavailable |
| `ThreePayloadCompile.reverse_delta_reconstructs` | applying the full-record delta reconstructs membership | `rr_replace_fingerprint` | source identity, sorting and canonical bytes need replay | authored; replay unavailable |
| `ThreePayloadCompile.reverse_delta_unrelated_consumer_preserved` | another consumer is unchanged | `rr_consumer_mismatch` | authenticated affected-domain/SCC authority OPEN | authored; replay unavailable |
| `ThreePayloadCompile.journal_exact_replay_idempotent` | exact record replay returns the same state | `journal_exact_replay` | exact bytes, checksum, i64 overflow and host durability OPEN | authored; replay unavailable |
| `ThreePayloadCompile.journal_conflicting_prefix_rejected` | a state matching neither accepted prefix is rejected | `journal_conflicting_prefix` | no crash-atomicity claim | authored; replay unavailable |
| `ThreePayloadCompile.protected_pin_not_swept` | a protected model object is never eligible | `gc_stale_epoch` | live races and transitive closure completeness OPEN | authored; replay unavailable |
| `ThreePayloadCompile.changed_source_binding_stale` | changed source hash rejects freshness | `source_binding_stale` | source-to-model/VIR translation OPEN | authored; replay unavailable |

“Authored” is not `ModelProven`. Each root becomes model evidence only after
the project gate builds and the emitted axiom lines pass the shared trust
auditor. The official Lean 4.30.0 AArch64 toolchain was identified and
provisioned. Three bounded gate cycles stopped at a parser error. That parser
expression was rewritten and Astra then identified a static `LawfulBEq`
obligation for `RrEdge`; both corrections remain unrerun under the mandatory
cycle cap. No theorem or axiom audit is admitted.

## Model boundaries

### Broker

`BrokerState` records pending roles, the attempted prefix, remaining budget,
successfully charged bytes, and failure. When no budget remains, the model
fails before appending a role. A missing or oversized outcome appends the
attempted role and fails; an oversized result is not charged. Conservation of
pending plus attempted roles establishes the read-count roots, while
conservation of remaining plus successfully charged bytes establishes the
byte root.

The existing physical broker relies on
`file_read_regular_no_follow_bounded`. If that foreign/facade boundary returns
more bytes than requested, the source refinement is invalid even though the
pure model remains true. The trace counts bounded facade invocations, not
kernel opens, reads, page faults, or syscalls.

### Reverse references

`reverseDelta` operates on full `RrEdge` values. Identity is the producer,
consumer, facet, and partition tuple; fingerprint and manifest changes replace
the old full record. The reconstruction theorem is a membership theorem, not a
canonical ordering or byte-codec theorem. Current source replay calls
`stage_reverse_delta_v1`; affected scheduling remains fail closed because
`plan_affected_queries_v1` has no authenticated domain authority.

### Journal and GC

The Lean journal is record-level state. It does not parse or checksum bytes.
The Simple replay calls the real `prepare`, `accept_durable`, and recovery
functions. `generation_manifest` remains an unsupported action-root journal
object kind and is asserted rejected; it must not be silently added to the
journal kind list.

A checksum-valid record missing only its final newline is deliberately
quarantined by the current recovery function. The parser has already counted
the logical newline, so `accepted_bytes` is one greater than the provided text
length. Therefore no theorem or test in this capsule asserts
`accepted_bytes <= input.length` without first excluding `quarantined_tail`.
Quarantined recovery never establishes visible-catalog authority.

The sweep theorem covers only the pure decision model. The source stale-epoch
fixture proves a fail-closed refusal, not a complete live pin/race proof.

## Current source links

Bounded replay calls existing owners rather than copying their algorithms:

- packer: `seal_three_payload_closure_v2`,
  `verify_prepared_three_payload_v2`;
- semantic adapter: `bind_three_payload_semantic_inputs`,
  `resolve_three_payload_semantic_input`;
- physical broker: `read_three_payload_physical_files_v1`;
- RR coordinator: `stage_reverse_delta_v1`, `plan_affected_queries_v1`;
- journal: `ActionRootJournalV1.empty`, `prepare`, `accept_durable`,
  `recover_action_root_journal_v1`;
- GC: `verified_generation_pin_snapshot_v1`,
  `verified_generation_sweep_decision_v1`.

The source-binding fixture names the production paths. At replay time the leaf
reads the current files through the bounded no-follow facade and hashes the
actual bytes. It binds every Lean proof module, the root, Audit, Lake file,
replay checker, broker, worker IO, file facade, selected cache contracts, packer,
semantic adapter, RR, journal, GC, and toolchain file. A fixture label or
stored prose hash is not source evidence. This explicit closure is still an
approximation; complete transitive compiler/effect closure remains OPEN.

## Replay cases

| Case | Required outcome |
|---|---|
| `broker_cold2` | two ordinary bounded facade reads, no RR/external read |
| `broker_warm3` | three ordinary bounded facade reads, no RR/external read |
| `broker_external_rejected` | external request rejected and affected evidence incomplete |
| `prepared_source_corrupt` | changed source bytes reject preparation; body authority remains unavailable |
| `rr_replace_fingerprint` | one old full record removed and one new full record inserted |
| `rr_consumer_mismatch` | invalid delta with no insert/remove |
| `journal_exact_replay` | second apply is idempotent and recovery is unquarantined |
| `journal_conflicting_prefix` | conflict rejected; `generation_manifest` kind unsupported |
| `journal_torn_final_newline` | record parsed but tail quarantined; accepted count may exceed input |
| `gc_stale_epoch` | sweep decision refused |
| `source_binding_stale` | changed current-source identity rejected |

Unknown case IDs return an unmatched observation.

## Verification state

The first prescribed Lean command established an environment RED because
`lake` was absent. Root then authorized the official Lean 4.30.0 AArch64
release in an isolated directory. The archive hash matched
`c99c6f0edd446956d4758c59d4383e8e6411ff6cc71a01f9caabe5eba454121d`;
Lake reported `5.0.0-src+d024af0` and Lean reported commit
`d024af099ca4bf2c86f649261ebf59565dc8c622`.

The gate was then run with explicit `LAKE_BIN`. Its third and final cycle
stopped before theorem elaboration at a multiline record-update parse error:

```text
FAIL verification/three_payload_compile --
src/ThreePayloadCompile/Model.lean:44:15: unexpected identifier; expected '}'
STATUS: FAIL lean-proof-check project
```

That expression was rewritten to a one-line update after the failure. Astra's
subsequent static inspection also identified that `RrEdge` needs explicit
`LawfulBEq` evidence for the generic membership lemmas; the structure now
derives it. The mandatory three-cycle cap prohibits another run in this
session. No proof was admitted and no axiom output was produced. The final
proof sources remain unverified and require a fresh reviewer gate.

The focused interpreter SSpec was not run. The current full CLI is the Rust
seed (`bin/simple`, reported hash prefix `3d120a6f`); the admitted Stage 2 hash
prefix `319c7bd2` is compiler-only, and Stage 3 failed. Using either as a
self-hosted full test runner would violate provenance. Consequently there is no
admitted replay, generated doc, model receipt, mutation receipt, or
`SourceRefined` evidence in this stage.

## Ownership

- Planner and architecture freeze: Astra (`/root/l7_formal_plan_astra`).
- Model/source/spec implementation: Sol (`/root/l7_formal_sol`).
- Independent proof-root and claim review: Astra.
- Merge/integration owner: root.

No production compiler/cache file, availability gate, shared umbrella plan,
commit, push, benchmark, or release artifact is changed by this capsule.

## 2026-09-11 three-file and invalidation audit

<!-- codex-architecture -->
<!-- codex-system-test: three-file-invalidation-audit -->

**Overall guarantee: MISSING; bounded components: PARTIAL; admission: CLOSED.**
This is a static source audit and proposed model extension, not a theorem,
executed counterexample, new runtime receipt, or permission to resume the
earlier capped proof run. Existing history above remains unchanged.

REQ-CSM-027 defines an *eligible strict-profile recompilation*, not every
compiler invocation. Its semantic payload inputs are `module.spl`, optional
prior `module.tld`, and effective `__init__.tld`: cold two, warm three. Catalog,
snapshot inventory and generation-pin reads are separately accounted control
operations. Compiler/toolchain loading, output writes and native linking must
also be explicitly classified; counting only successful facade calls does not
prove all process IO is confined. RR is mutation-time routing, never a fourth
semantic worker input. An ineligible action may take a separately recorded
conservative compile path, but cannot retain the three-file success claim.

### Current source assessment

| Required property | Observed implementation | Disposition |
|---|---|---|
| Ordinary compilation reads only the three payloads | `driver_source_pipeline_loading.spl:254–378` discovers and loads the entry's transitive source imports. The restricted broker is not this ordinary source loader. | MISSING globally; planned strict-profile boundary only. |
| Cold two / warm three, with no worker RR | `three_payload_physical_file_broker_v1.spl:110–165` performs bounded source/prior/init reads, validates the reconstructed physical snapshot and rejects RR/external policy. Its activation gate remains false at 196. | PARTIAL: real facade path, not admitted full compilation or OS-level confinement. Distinct path strings do not prove distinct file identities or resistance to hard-link/parent-path aliasing. |
| Complete affected set from changed facets and old/new membership | `reverse_reference_coordinator_v1.spl:589–592` keeps domain authority false; the ordinary planner at 735 supplies nil authority. Shape-valid roots and empty matches cannot authenticate absence. | Safe refusal exists; productive mutation scheduling MISSING. |
| Exact old RR history replacement | V1 staging at `reverse_reference_coordinator_v1.spl:1035–1050` permits nil old history; its delta helper treats it as no removals. V2 model requires non-genesis history, while production preparation at `reverse_reference_atomic_generation_v2.spl:343–350` refuses without real history authority. | V1 candidate gap; V2 model is not a live publisher. |
| Recompute trait/aspect/macro/body effects before reuse | `semantic_scope_issuers_v2.spl:626–636` returns Unknown/incomplete/unavailable. Sampled owner revisions are not complete source-universe or conditional-dependency authority. | CLOSED; no positive semantic-completeness claim. |
| Unchanged effective summary permits exact reuse | `driver_build/incremental.spl:1031–1049` checks own-source/output/dependency-interface freshness; `cache/action_key.spl:257–287` explicitly omits field layout from its textual interface. | PARTIAL legacy optimization; insufficient for semantic facet soundness. |
| Atomically publish a complete generation before affected consumers | `three_payload_generation_publisher_v1.spl:223–274` validates a candidate before one in-memory active assignment; availability and reader-pin commit guard remain false at 776–799. | PARTIAL transition checks, not host durability or atomic pin/commit proof. |

The source inventory above was read from the shared worktree at HEAD
`c2f542538de94d06c5948b933263487965fc6577`; several files are untracked or
modified, so HEAD alone is **not** their provenance. Frozen observed SHA-256:

| Source suffix (under `src/compiler/`) | SHA-256 |
|---|---|
| `80.driver/driver_source_pipeline_loading.spl` | `15eeaee97a04b4ee6b37e1b0433fe370606c93916455c56dc7572fed638dd9ef` |
| `80.driver/cache/worker/three_payload_physical_file_broker_v1.spl` | `cc1b9297d321bbc503529d396fa424ccd8310c46e9f33c6a16b207564f35bfb9` |
| `80.driver/cache/reference/reverse_reference_coordinator_v1.spl` | `b2a011bfc9debd47ec9094f9abdd664ee2988d76b555979837fb963270c7c2d4` |
| `80.driver/cache/reference/reverse_reference_atomic_generation_v2.spl` | `a3e076f8a8275506468357c43dc0f3717ecc876eb2e6f3db0e92c3aa7ab49ad2` |
| `35.semantics/semantic_scope_issuers_v2.spl` | `9184d5d7e39d12368f4f3fc7188b58bf4856fb4936a64eb9edc4104a978be12b` |
| `80.driver/cache/action_key.spl` | `37ac46b1042883938e42d10d28438f1c877198b30d80448f90f7da01d348f079` |
| `80.driver/driver_build/incremental.spl` | `9f4f8ed66e81013e98e7c30e1fae8da97334ab7e11e1579691988a521f3f1965` |
| `80.driver/cache/publication/three_payload_generation_publisher_v1.spl` | `8bcf5b2e335147e93d3f8a7be38a47f6ae5da2aac2e17ab5f7e308f3add1c340` |

### Proposed state machine and invariants

Use the existing model capsule; the following names are proposed obligations,
not existing Lean declarations. Let generation `G` own immutable summaries `S`,
forward reads `F`, reverse routes `R`, object roots `O`, and complete membership/
absence evidence `M`. An edge names producer, consumer, consumed facet,
fingerprint, partition and exact forward-manifest identity. Fingerprints stand
for canonical semantic values under an explicit collision-resistance and
schema-completeness assumption; string equality alone is not semantic proof.

```text
Pinned(G) -> MutationInventory(G, change)
          -> AffectedClosure(G, F, R, M)
          -> RecomputedCandidate(G+1, S', F', R', O', M')
          -> DurablePrepared(expected_parent=G)
          -> PublishCAS(G -> G+1) -> AdmitConsumers(G+1)
Pre-linearization refusal -> no publication by this attempt
Successful CAS / unknown acknowledgment -> resolve durable commit identity
```

Before linearization, incomplete authority, conflict or cancellation publishes
nothing from this attempt: `G` remains its pinned input, not necessarily the
current active generation. Another publisher may already have installed `H`.
After successful CAS, cancellation cannot undo the commit. An unknown outcome
must be resolved against the durable commit identity before reporting committed
or refused; never restore or report `active=G` merely because acknowledgment
was lost or cancellation arrived.

Recomputation is coordinator work against a frozen prospective snapshot, not
an ordinary consumer observing half-published summaries. Unrelated readers
may finish against a still-pinned `G`; affected readers either stay wholly on
their admitted old snapshot or wait/restart for `G+1`. Publication cannot mix
new summaries with old forward/RR roots. SCCs are recomputed to a validated
fixed point or conservatively rejected, never scheduled as independent cycles.

1. `ordinary_payload_confinement`: every attempted semantic input read by an
   admitted worker has one permitted role and pinned identity; RR/CAS/imported
   sources/network/ambient macro IO are denied before a result. Successful
   role counts are two or three; failed attempts are counted separately.
2. `forward_reverse_generation_bijection`: for each admitted forward read,
   exactly its full reverse edge exists in the same generation, and vice versa.
   Nil history is not a complete empty history. Missing RR is not an empty set.
3. `affected_closure_sound`: any changed consumed facet, or changed candidate/
   absence membership capable of altering lookup, reaches every old or new
   consumer through authenticated old/new union and transitive/SCC closure.
4. `facet_reuse_sound`: reuse requires complete current witnesses and equality
   of **every actually consumed** effective facet, plus target/compiler/action
   identities. Equal public signatures alone are insufficient. An unchanged
   call-only body may preserve a caller object; a changed consumed generic,
   macro/CTFE/default/advice body or scope-selection facet must invalidate it.
5. `publication_linearization`: candidate roots remain invisible until all
   objects/journal/checkpoint and commit-scoped authority validate; the active
   parent comparison and root replacement form one host-authorized transition.
   Pre-commit refusal leaves active state unchanged by this attempt; post-commit
   cancellation and lost acknowledgment resolve the durable commit outcome
   without rollback or a false refusal claim.
6. `refusal_no_false_reuse`: Unknown/Partial/missing/corrupt/stale evidence
   yields no hit and no partial publication. A conservative fallback must
   rebuild a proven complete enclosing domain, or fail; an empty work list is
   not itself safe fallback evidence.
7. `recovery_generation_coherence`: crashes before/after the linearization
   point recover one wholly committed generation; prepared-only roots are not
   active. In the single-publisher model this is `G` or `G+1`; with competing
   publishers, recovery follows durable commit order, not the losing input pin.
   Model recovery is not storage-fault/power-loss evidence.

### Counterexamples that the stronger model/tests must kill

| Counterexample | Failure that must be observable |
|---|---|
| Active RR has `A -> consumer C`; pass nil old history and new reads only from B to V1 staging. | A can remain while B is inserted because no A removal was derived. Reject absent authenticated old history, including the zero-edge-but-existing consumer case. This is a candidate-level source gap, not an admitted publication receipt. |
| Rename/retype a dependency struct field without changing declaration headers; caller source and output existence stay unchanged. | Textual interface digest can remain equal and the local legacy cache predicate can accept. Require field/layout consumption fingerprints or conservative miss; do not call textual equality full summary equality. |
| Add a trait implementation/aspect selector/macro candidate outside the formerly nonempty match set, or change a formerly empty match. | Routing only old positive edges misses new/zero-match consumers. Exact candidate-domain and absence witnesses must invalidate them. |
| Keep a signature stable but change consumed macro/default/generic/body-observing advice code. | A signature-only key produces false reuse. Consumed body closure must change; ordinary symbolic call-only bodies are a separate case. |
| Replace a valid RR shard with missing/partial data and interpret absence as no consumers. | No affected-set/hit receipt; conservative complete-domain fallback or exact refusal. |
| Publish new summary before its forward/RR/object roots, or revoke the reader/writer lease between validation and active assignment. | Mixed-generation lookup or stale-authority commit; require commit-scoped guard and one coherent root switch. |
| Cancel after successful CAS, lose the commit acknowledgment, or lose CAS because another publisher installed H. | Never restore/report active G on cancellation or conflict. Test cancellation on both sides of linearization, durable commit-identity resolution after lost acknowledgment, and a losing attempt leaving H untouched. |
| Two admitted role paths alias one physical object, or a failed fourth read is omitted from a success-only receipt. | Role-count theorem may pass while physical confinement fails; require owner-recorded attempted IO and identity/alias evidence. |

### Property and SSpec obligations (not implemented by this audit)

Reserve `FV-L7-I001`–`FV-L7-I007` for the seven invariants above, in order.
They trace to REQ-CSM-001/002/003/005/006/008/012/026/027/029 as applicable;
they do not add acceptance points to the historical L7 ledger. Each obligation
needs a positive, boundary and negative case, independently labeled model,
component, integration or production E2E. Use consistent
`[importance=critical; importance_weight=3]` metadata; execution P/F/E/U and
model/source-refinement status remain separate. All new obligations are OPEN,
execution U, branch coverage UNMEASURED; target >=95% per executable component
and 100% critical refusal decisions, not a claimed percentage.

Extend the existing Lean Model/Broker/ReverseReferences/Publication/SourceLink
modules and the existing
`test/00_formal_verification/compiler/three_payload_compile_refinement_spec.spl`
only after exact source/fixture/interface allocation. Reuse the physical broker,
P5, atomic-generation model, affected-domain authority, reference-aware body,
and publication-transition specs already named in the activation plan; preserve
the original eight `L7E2E-*` scenario meanings and their weight allocation.
Mirrored manuals follow the exact spec-relative path under `doc/06_spec/`.
The nine historical roots remain the existing capsule; the stronger obligations
must not silently replace or inflate them.

Freeze future visible steps: `Pin one coherent generation`, `Apply one scoped
semantic mutation`, `Recompute the authenticated affected closure`, `Publish or
refuse one coherent generation`, `Verify exact reuse and confined consumer IO`.
Keep current fixture/helper APIs until the implementation owner freezes the
additional signatures; no generic helper may manufacture completeness, mutate
an active root directly, or turn MissingEvidence into success. Mutation receipts
must name the exact changed source/model bytes and failed assertion, not merely
record that a fixture ran.

Acceptance sequence: qualify the runner and dependency closure; elaborate the
model and audit all root axioms; execute real source mutation/replay; exercise
host crash/lease/IO tests; independently review source refinement and zero-stub
manuals; only then consider activation. The existing Lean command in the agent
plan stays a future gate, not a rerun authorization. Its historical interpreter
command is not proof that scenario bodies executed: select a qualified mode and
retain per-scenario/branch evidence. No production, Lean or SSpec code changed
in this audit.

Related contracts: [strict-profile activation](../03_plan/sys_test/l7_l8_three_file_compile_activation_contract.md),
[RR atomic generation](../05_design/reverse_reference_atomic_generation_v2.md),
[requirements](../02_requirements/feature/compiler_semantic_cache_daemon_virtual_summary.md).

### 2026-09-11 bounded implementation follow-up

The implementation candidate based on this audit adds authored, unadmitted
evidence for parts of `FV-L7-I001`, `I002`, `I004`, `I005`, and `I007`:

- genesis RR seeding is separate from mutation routing; mutation rejects nil
  old history and accepts an explicit complete-empty manifest;
- a diagnostic semantic-facet DTO/diff schema represents callable signatures, ordered
  fields/layout, aspect call signatures/advice/candidate/absence, macro
  signatures/bodies/inputs, and trait signatures/candidate/absence; its
  coverage digests are untrusted shapes, not authenticated source witnesses;
- the strict physical broker exposes cold-two/warm-three payload evidence while
  an explicitly untrusted diagnostic DTO keeps catalog and generation-pin
  counts separate; it does not connect a live control owner;
- durable outcome resolution reopens the checkpoint and reports the actual
  durable active generation, including committed-superseded outcomes after
  cancellation or lost acknowledgment; and
- additive Lean roots model absent versus explicit-empty RR history, atomic
  nonempty record shape, competing publication, and post-CAS resolution. The
  shape model does not bind a manifest to its roots or authorize a transition.

These are contract/model/component changes, not completion of the global
invariants. Common-contract provenance, live semantic issuers, authenticated
old-history ownership, host commit authority, physical alias evidence, Lean
execution, SSpec execution, and activation remain OPEN. All availability gates
remain unchanged and fail closed.
