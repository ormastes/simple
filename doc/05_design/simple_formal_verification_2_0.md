<!-- codex-design -->
# Simple Formal Verification 2.0 Detail Design

**Status:** FV2 implementation restored and reconciled; executable admission blocked
**Date:** 2026-08-14
**Architecture:** `doc/04_architecture/simple_formal_verification_2_0.md`

## Frozen implementation and manual vocabulary

Implementations and tests consume the ten exact V1 interface names defined by
the architecture: `VerificationIR`, `SemanticCoverage`, `ProofObligation`,
`ProofReceipt`, `TrustManifest`, `WeaveManifest`, `CompilerCertificate`,
`HardwareProofReceipt`, `FormalStatus`, and `VerificationCacheKey`. Changes to
their canonical shape are version changes, not local refactors.

The frozen display names map to implemented Simple symbols as follows. The display
name is the public contract; spelling a code symbol differently does
not rename or supersede it.

| Frozen display name | Simple symbol/owner | Working tree |
|---|---|---|
| `VerificationIR v1` | `VerificationIrV1` in `src/compiler/50.mir/verification_ir.spl` | Implemented |
| `SemanticCoverage v1` | `SemanticCoverageV1` owned by the VIR builder | Implemented |
| `ProofObligation v1` | `ProofObligationV1` in common assurance | Implemented |
| `ProofReceipt v1` | `ProofReceiptV1` in common assurance | Implemented |
| `TrustManifest v1` | `TrustManifestV1` in common assurance | Implemented |
| `WeaveManifest v1` | `WeaveManifestV1` in common assurance | Implemented |
| `CompilerCertificate v1` | `CompilerCertificateV1` in common assurance | Implemented |
| `HardwareProofReceipt v1` | `HardwareProofReceiptV1` in common assurance | Implemented |
| `FormalStatus v1` | `FormalStatusV1` in common assurance | Implemented alias |
| `VerificationCacheKey v1` | `VerificationCacheKeyV1` in common assurance | Implemented |

The primary generated-manual flow uses exactly:

- `step("Audit the formal claim boundary")`
- `step("Construct canonical verification evidence")`
- `step("Reject stale or unsupported evidence")`
- `step("Replay the shipped artifact independently")`

Shared helpers are exactly `setup_fv2_fixture`, `check_fv2_gate`, and
`check_fv2_replay`. Until a helper owns a real oracle it must call `fail(...)`.
The generated manual must expose the four operator-facing steps and fold setup
mechanics and secondary matrices; raw test code is not the primary manual.

## Current executable blockers

- The canonical `bin/release/x86_64-unknown-linux-gnu/simple` Stage 4 CLI and
  generated `bin/simple` launcher are unavailable in this worktree. The
  fallback release artifact identifies itself but rejects `-c` and segfaults
  during the bounded `test --help` ABI probe. No seed or static-only result may
  replace the missing self-hosted acceptance run.
- MIR backend closure is not complete until all consumers explicitly preserve,
  lower, or reject `DecisionProbe` and `ConditionProbe`. Native x86_64,
  AArch64, RV32, and RV64 selection must panic with the semantic identity when
  an unlowered probe arrives; neither the named `Nop` arm nor a wildcard
  unsupported arm may consume it. Executable proof of those paths waits on the
  repaired Stage 4 runtime.
- Until both blockers close, status is `blocked`/`unsupported` at the affected
  edge and cannot be promoted to `backend_refined` or `artifact_verified`.

## Current-tree artifact and status inventory

This table is authoritative for implementation claims in this document. Every
statement after it is normative proposed behavior, even when written in the
present tense for specification clarity, unless a row here explicitly says
`Present`. No named collector, V1 record, replay/release adapter, cache owner,
or product-proof flow below is a current-tree implementation claim.

| Artifact | Current status | Admissible evidence |
|---|---|---|
| `src/compiler/50.mir/mir_instruction_kinds.spl` | Present: typed probe variants | Static source plus focused spec; executable rerun blocked |
| `src/compiler/50.mir/mir_coverage_probe_admission.spl` | Present: fail-closed admission | Static source plus focused spec; executable rerun blocked |
| `src/compiler/50.mir/mir_json.spl` | Present: deterministic probe serialization | Static source plus focused spec; executable rerun blocked |
| MIR optimizer/visitor/SSA/DCE probe preservation | Present in current lane, not runtime-admitted | Static inspection only until Stage 4 recovers |
| Interpreter, LLVM, llvm-lib, WASM probe rejection | Present/partial | Static inspection and existing focused specs; runtime blocked |
| Native x86_64/AArch64/RV32/RV64 probe rejection | Present in commit `27fa51e3ae0`; not executable evidence | Blocked on Stage 4 CLI and backend closure gate |
| `test/01_unit/compiler/mir/mir_coverage_opcode_admission_spec.spl` | Present | Not rerun: authoritative runtime unavailable |
| Frozen V1 interface implementation files | Present in working tree | Static shape evidence; runtime blocked |
| Gate 0–7 collectors and finalizer | Present in working tree | Runtime verification blocked |
| Fresh/independent FV2 replay scripts and pinned adapter | Present in working tree | External tool execution blocked |
| FV2 release CLI, signature adapter, signer policy | Present in working tree | Signed-bundle execution blocked |
| RV32 ADD end-to-end/equivalence/Sail machinery | Present in working tree | External tool/product evidence blocked |

## Requirement-to-design traceability

Every selected requirement has a proposed owner and evidence target. `Planned`
means the design is normative but the named current-main implementation does
not exist. `Partial; blocked` means bounded source exists but cannot satisfy the
requirement or be re-admitted without the Stage 4 runtime.

| ID | Design section | Proposed module/owner | Executable test/evidence target | Current status |
|---|---|---|---|---|
| REQ-FV2-001 | Core records | `compiler.common.assurance.formal_status` | status-lattice and false-promotion negatives | Planned; blocked |
| REQ-FV2-002 | Policy versioning | assurance policy V2 resolver | profile resolution plus V1/V2 confusion negatives | Planned; blocked |
| REQ-FV2-003 | Canonical lowering algorithm | frontend weave owner + VIR builder | same canonical-program hash through proof/build | Planned; blocked |
| REQ-FV2-004 | Contract VC shape | MIR contract bridge | normal/error execution-linked VC scenarios | Planned; blocked |
| REQ-FV2-005 | Core records | `verification_ir.spl` | canonical VIR round-trip and mutation negatives | Planned; blocked |
| REQ-FV2-006 | Type/effect design | MIR probe bridge + VIR semantics | `mir_coverage_opcode_admission_spec.spl` and width edges | Partial; blocked |
| REQ-FV2-007 | Lean and solver design | typed Lean IR owner | typed emission plus guessed/fallback rejection | Planned; blocked |
| REQ-FV2-008 | Contract VC shape | obligation DAG builder | thirteen-kind ordering/dependency/closure tests | Planned; blocked |
| REQ-FV2-009 | Lean and solver design | replay and axiom-audit adapters | fresh + independent exact-root replay negatives | Planned; blocked |
| REQ-FV2-010 | Core records | receipt/trust/cache owners | canonical hash, drift, duplicate, stale mutations | Planned; blocked |
| REQ-FV2-011 | Canonical lowering algorithm | weave-manifest owner | join-point/order/post-VIR transform negatives | Planned; blocked |
| REQ-FV2-012 | Type and effect design | MIR region/effect closure | transitive direct-call and unknown-call negatives | Planned; blocked |
| REQ-FV2-013 | Canonical lowering algorithm | compiler certificate validators | gap-free pass/target certificate chain | Planned; blocked |
| REQ-FV2-014 | Product flows / SimpleOS | SimpleOS gate adapter | implementation-linked seven-subsystem receipts | Planned; blocked |
| REQ-FV2-015 | Product flows / RISC-V | HWIR/RVFI/Sail/SBY/equivalence adapters | RV32 ADD then RV64 product chain | Planned; blocked |
| REQ-FV2-016 | Security/failure rules | mutation and non-vacuity owners | property/implementation/cache/evidence mutants | Planned; blocked |
| REQ-FV2-017 | Core records | dynamic composition/trust adapter | signed receipt compatibility and TCB negatives | Planned; blocked |
| REQ-FV2-018 | Canonical lowering algorithm | existing verification syntax owners | grammar census and no-new-syntax guard | Planned; blocked |
| REQ-FV2-019 | Current executable blockers | every producer/consumer boundary | probe admission/backend rejection plus timeout/tool negatives | Partial; blocked |
| REQ-FV2-020 | Gate design | planned Gate 0–7 collectors/finalizer | ordered predecessor and premature-pass negatives | Planned; blocked |
| NFR-FV2-001 | Caching and scheduling | canonical serializers/tool pinning | clean rebuild identity comparison | Planned; blocked |
| NFR-FV2-002 | Diagnostics | all reducers/adapters | unsupported/stale/timeout/unknown fail-closed matrix | Partial; blocked |
| NFR-FV2-003 | Core records | trust-manifest owner | complete attributable trust closure | Planned; blocked |
| NFR-FV2-004 | Caching and scheduling | SCC scheduler/cache owner | formatting-only hit and dependency invalidation | Planned; blocked |
| NFR-FV2-005 | Canonical lowering algorithm | weave/VIR/Lean/receipt emitters | repeat-run byte/hash determinism | Planned; blocked |
| NFR-FV2-006 | Caching and scheduling | scheduler/batched engine runners | warm timing, cache metrics, startup count, max RSS | Planned; blocked |
| NFR-FV2-007 | Diagnostics | source/OS/RTL trace mapper | mapped counterexample fixtures | Planned; blocked |
| NFR-FV2-008 | Frozen interface mapping | schema/version migration owners | incompatible-version and stale-cache tests | Planned; blocked |
| NFR-FV2-009 | Lean/RISC-V product flows | independent replay + Sail owners | checker independence and oracle identity evidence | Planned; blocked |
| NFR-FV2-010 | Caching and scheduling | DAG/SCC scheduler | independent-shard parallelism and deterministic join | Planned; blocked |

## Core records

Planned executed-evidence collectors follow product ownership boundaries:
`formal_gate_collectors` owns core Gates 0–3,
`formal_os_hardware_gate_collectors` owns SimpleOS/RV32 Gates 4–5, and
`formal_product_gate_collectors` owns RV64/release Gates 6–7. Product adapters
would consume these interfaces; none may redefine the frozen status, receipt,
or gate schemas. These collector modules are absent on current main.

The proposed implementation would use immutable versioned records with canonical serialization. IDs are content-derived except `SymbolId`, which remains stable across formatting and unrelated edits. Receipts refer to hashes, never mutable filesystem paths as identity.

Planned replay orchestration is split by checker authority. The proposed
seven-root fresh lane is
`scripts/check/run-fv2-simpleos-fresh-replay.shs`; it runs exact Lake modules
through `leanchecker --fresh` and may synthesize a hash-bound attestation only
for silent exit-zero fresh-kernel success. The independent lane is provisioned
by `scripts/setup/setup-fv2-independent-replay.shs` and executed by
`scripts/check/run-fv2-simpleos-independent-replay.shs`; it exports each exact
declaration root through the pinned format-v2 exporter and checks it with
nanoda. It retains per-root output and emits an accepted aggregate only when
all roots pass. Any partial success emits diagnostic rejected evidence, never a
Gate 4 receipt. Both lanes bind the exact post-build module `.olean` hash as
the replay artifact identity and retain the theorem source hash separately;
source identity alone cannot hide drift in imported declarations. Closed
verification keeps nanoda Nat/String extensions disabled;
an exported `#ELN`/`#ELS` dependency is therefore a typed capability rejection,
not permission to widen the TCB silently.
The adapter itself enforces a lowercase 64-character SHA-256 artifact identity
and repeats the exact declaration root in its accepted attestation; caller-side
validation is defense in depth, not the trusted identity boundary.
Retained exporter inputs are keyed by module, declaration root, and artifact so
two roots from one `.olean` cannot overwrite each other's replay material.
When implemented, fresh replay resolves the exact checker and Lake launcher
once, invokes those
resolved paths, and hashes both; version evidence cannot accidentally describe
a different PATH-resolved binary from the one that performed replay.

`VerificationIR` contains declaration records and an explicit transition graph. Each declaration stores source/expanded/woven hashes, exact representation, typed effects, ownership/capabilities, contracts, termination measure, called-symbol IDs, trust references, and semantic class. `ProofObligation` references VIR node IDs rather than re-parsed text.

`FormalStatus` is a lattice, not a Boolean. Aggregation chooses the least-assured reachable node; `failed`, `unsupported`, `stale`, and `admitted_development` always block. `trusted_boundary` can close only under a profile policy that permits its exact manifest class; a closed verified label additionally requires zero project axioms and no unchecked external result.

### Policy versioning

`verified` is not added to frozen `AssuranceStrictness`/PolicyV1. FV2 uses
`AssuranceStrictnessV2` and `ResolvedAssurancePolicyV2`; the latter has an
independent `APOLV2-*` canonical hash and a raise-only resolver over project,
CLI, and subprocess inputs. V1 consumers project `verified` to `critical`
only for engineering restrictions. Receipt promotion requires a V2 policy with
strictness exactly `verified`; a V1 critical projection is never sufficient.

## Canonical lowering algorithm

1. Resolve names/types and compute typed direct effects.
2. Expand macros deterministically and record introduced SymbolIds.
3. Resolve AOP selectors to ordered SymbolIds; weave and record `WeaveManifest`.
4. Re-run type/effect/ownership checks on the woven HIR.
5. Compute transitive calls/effects and verified closure.
6. Lower each reachable construct through exhaustive typed VIR visitors.
7. Validate `SemanticCoverage`; reject unsupported/default/fallback paths.
8. Emit typed Lean IR and other engine jobs from VIR.
9. Compile the same canonical program and validate each selected lowering.
10. Join proof, compiler, runtime-monitor, and artifact identities into a final receipt.

## Contract VC shape

For each function and all initial states/arguments:

```text
WellFormed(pre_state, args)
and Requires(pre_state, args)
and Exec(function_id, pre_state, args) = outcome
implies Ensures(pre_state, args, outcome)
```

`Ensures` dispatches on `Ok(ret, post_state)`, `Err(err, post_state)`, trap, cancellation, or divergence policy. Frame VCs prove non-modified regions unchanged. Preconditions additionally receive satisfiability witnesses; invariants receive reachable witnesses.

The proposed pure-function Lean slice would emit two roots when `in:` is present:
`<function>_preconditions_satisfiable` and `<function>_spec`. With
`proof uses: X`, generated proofs reference `X_preconditions_satisfiable` and
`X`, respectively; both enter transitive trust audit. Predicate roots retain
exact source spans and internally derived semantic hashes. The proposed
stateful design assigns typed `ExecutionContractObligation v2` ownership (the
frozen v1 shape remains the compatibility boundary): invariant initialization
requires a reachable-state
semantic identity, preservation requires a transition identity, frame VCs
require transition plus region-model identities, and decreases VCs require
recursive-call plus well-founded-order identities. Preconditions likewise need
an exact input-domain identity before their satisfiability VC exists. Each VC
records the authorities and a derived relation-semantic hash; missing authority
fails closed. V1 refuses clauses that need authorities it cannot represent.
The proposed canonical MIR bridge would reject a caller-selected execution hash and derive
the precondition input-domain identity from the exact SymbolId, parameter-type
serialization, arity, and variadic policy.

Proof receipts distinguish the exported generated root from its external proof
dependency. The receipt root is always the theorem or definition emitted in the
generated namespace (for termination, the recursive definition itself); its
dependency set must additionally contain the derived `proof uses` root such as
`X_termination` or `X_invariant_preservation`. Substituting the external helper
as the receipt root is rejected. The matching cache key independently binds the
exact MIR execution hash and obligation hash, so a same-named proof from a
different obligation cannot be promoted.
Contract proof promotion also consumes the materialized `TrustManifestV1` and
requires its canonical hash to match the proof receipt and its boundary lists to
be closed. A nonempty caller-authored trust string is not evidence.
The trust-audit parser and canonical audit hash live in common assurance so MIR
promotion can parse the retained `#print axioms` output itself. It requires one
closed exact-root report whose canonical audit hash binds the same theorem
artifact; an opaque or copied audit-hash string cannot promote the obligation.
Logical clauses require exact `bool`; `decreases` instead requires an exact
unsigned fixed-width measure (`u8` through `u128`) so strict unsigned decrease
is finite and well-founded. Boolean and signed measures fail closed. For direct
recursion, the bridge derives the exact serialized self-call set and canonical
unsigned-order identity; forged call/order identities fail. Product invariant
and frame generation for effectful code remains rejected until canonical heap,
region, and external-transition owners exist. For the exactly classified pure
subset, the proposed canonical MIR bridge would derive reachable input states, a `Unit` identity
transition, and an empty frame. Only local computation, pure control flow,
self-recursion, and the exact Result constructor/discriminator/payload
primitives enter this class; load/store/global mutation, allocation, indirect
or unknown calls, traps, unwind, synchronization, and external boundaries fail.
The proposed canonical Lean backend would render typed direct-call operands as validated Lean
identifiers rather than string literals. A retained unsigned `decreases`
expression emits `termination_by measure.toNat`; it requires `proof uses: X`
and discharges decreasing goals only through the audited derived root
`X_termination`. Missing or malformed roots fail. Lean state-transition theorem
receipts deliberately audit the generated definition/theorem root (for example
`Module.recursive` or `Module.stateful_invariant_preservation`) because that is
the exported artifact root; the receipt must also list the exact `proof uses`
root (`X_termination` or `X_invariant_preservation`) as a transitive dependency.
Issuance additionally requires one materialized verified cache key whose VIR
hash equals the obligation's MIR execution identity and whose contract hash
equals the exact obligation hash. A same-named proof from another MIR body or
obligation therefore cannot be reused. Lean state-transition theorem
emission is planned to cover pure invariant initialization/preservation and an
axiom-free empty-frame theorem over the actual function call for every
classified pure exported definition, including functions without source
contracts; effectful
invariant/frame emission remains pending. Source `Result<T,E>`
types and direct typed `Ok`/`Err` construction retain exact payload and variant
identity through MIR and lower to `Except`. The canonical pure `?` early-return
shape is validated and structured as an `Except` match; general propagation,
deep matching and stateful/nested control flow remain pending. Exhaustive
shallow Result matches use a typed ghost MIR witness that runtime backends erase
but Lean accepts only after revalidating the actual discriminator chain,
payload extraction, arm copies, merge, and impossible fallthrough edge.

## Type and effect design

- `iN/uN` lower to exact bit vectors plus signed interpretation where required; checked, wrapping, and saturating operators remain distinct VIR operations.
- Runtime text is bytes plus UTF-8 invariant; ABI/layout relations are separate from logical views.
- Mutable values lower to heap/state transitions with region capabilities.
- async lowers to an explicit state machine with cancellation and event traces.
- extern/SFFI/MMIO lower to explicit contracted transitions, never generated axioms.
- Typed effects include pure, region read/write, allocate/free, IO, time, random, spawn/suspend, atomic order, FFI capability, MMIO region, and unsafe capability.

The planned `MirRegionEffectManifest v1` is the canonical direct-effect owner
for the first admitted stateful subset. When implemented,
`LoadGlobal`/`StoreGlobal` produce exact
`global:<SymbolId>` read/write effects with serialized MIR value types and
instruction hashes plus exact source spans; missing provenance or inconsistent
types fail. Pointer/heap operations without a
region/capability, indirect or unknown calls, device/synchronization operations,
and trap/unwind terminators remain unsupported. VIR derives effects from this
manifest and rejects any caller-supplied effect set that disagrees. The
frame-model hash includes the exact sorted written-region-and-type set. A
`MirRegionFrameObligation v1` binds execution, open typed-state model,
transition, frame, and written-region identities; it is an obligation identity,
not by itself a proof. The Lean 4.33 `MirRegionFrame.run_frame` theorem proves
that a typed global read/write sequence preserves every region outside its
derived write set. Per-function promotion consumes a typed `ProofReceiptV1`
for that exact model root and additionally requires theorem artifact, cache,
axiom-audit, closed-trust, and independent-replay identities. The resulting
receipt is capped at `source_refined`; compiler/backend/artifact refinement is
still required.

`VerificationObligationClosureV1` is the engine-neutral closure protocol. Its
generator emits each `ProofObligationKindV1` exactly once in a deterministic
topological order. Validation rejects missing/duplicate kinds, duplicate IDs,
external or forward edges, an absent proposition hash, and any final root other
than `TrustClosure`. The closure hash includes every node, proposition identity,
and dependency edge. The generic protocol accepts typed authority hashes for
engine-neutral use. The canonical MIR adapter instead derives them from
retained contracts, serialized signatures and execution, region/effect
manifests, exact self-call closure, backend identity, and a closed trust
manifest. Its initial admitted subset includes finite acyclic CFGs (validated by
exact block/edge closure and cycle detection), or direct self recursion with
retained well-founded decreases evidence; indirect calls, module calls, and
cyclic CFGs without a retained measure fail closed.
Proof discharge remains required before REQ-FV2-008 can be considered complete.

The planned `verification_obligation_module.spl` adds the first canonical
inter-function composition. Its migration-only V1 path remains model evidence only. The
verified candidate is `ResolvedCanonicalModuleClosureV2`: it consumes a
`ResolvedDirectCallManifestV1` made from resolver-captured direct-call
`SymbolId`s and materialized only after the final MIR module exists, when exact
call-site, signature, and callee-body hashes can be computed. It binds that
manifest hash to the closure and `ResolvedVerificationIrModuleV2` consumes the
same manifest for effects and called-symbol IDs. Textual callee names are only
a consistency check; they never establish a callee identity. A canonical
frontend producer must capture each resolver decision during lowering and
finalize the manifest post-MIR/pre-VIR. Until that producer is connected, the
V2 adapters cannot certify ordinary source programs. Missing or duplicate
bindings, stale module/signature/body snapshots, indirect targets, effectful
callees, nested calls, or call terminators fail closed; this prevents
direct-only frame evidence from hiding a callee's effects while transitive
SCC/region composition remains unfinished.

`verification_call_manifest_finalizer.spl` is the post-MIR owner for that
materialization. Its input is positional resolver capture
`(owner SymbolId, block id, instruction index, callee SymbolId)` plus a
resolver receipt hash; its output recomputes every binding against the final
MIR snapshot and immediately revalidates the complete manifest. It does not
turn generated/runtime calls into forged internal bindings. Such a call must
first receive an explicit external-boundary contract; otherwise finalization
fails closed. The still-pending lowering integration owns capture production
and the driver owns retaining the resulting manifest before VIR construction.

The external-boundary extension is explicit and resolver-originated: every
direct call site must partition into one `Internal(callee SymbolId)` binding or
one `External(boundary id, ABI identity, effect-contract identity)` binding.
MIR deliberately omits extern declarations, so a post-MIR `rt_*` prefix is not
authority to infer either class. Finalization must reject missing, duplicate,
or overlapping rows; an accepted external row supplies the existing typed
`FFI(capability)` effect and an approved contract/trust reference. This work is
required before a real lowered module with generated/runtime calls can enter
the resolved V2 closure.

`VerificationObligationEvidenceClosureV1` validates discharge evidence without
promoting it beyond `model_proven`. It requires one exact discharge per
obligation, exact closure/proposition/root bindings, theorem artifacts, trust
and independent-replay identities, and every direct DAG dependency in the
consumer theorem's dependency set. Missing, duplicate, drifted, unreplayed, or
dependency-incomplete receipts fail the whole evidence closure. This protocol
does not fabricate proofs; executed Lean generation and replay must supply the
thirteen discharges. One theorem may discharge multiple propositions only when
its receipt binds every corresponding obligation/proposition identity.

`ProofUsesClosureManifestV1` reuses the existing `proof uses` channel without
adding grammar. One exact qualified base theorem expands into a stable theorem
family for type, satisfiability, termination, ownership, frame, invariants,
calls, non-vacuity, lowering, and trust; normal/error outcomes may share the
base theorem when its checked statement covers both branches. Evidence closure
requires the generated theorem receipt to list the exact expanded external
dependency. Invalid names, missing dependencies, or closure drift fail closed.

The planned `evaluate_verified_release_v1` is a deterministic final fail-closed reducer.
It requires the `verified` profile, `artifact_verified` final status, exact
artifact/evidence identity, nonempty unique proof and compiler-certificate
sets, trust, independent replay, mutation, and non-vacuity receipts, and a
closed reachable-symbol status set. `unknown`, timeout, missing tool, tool or
environment failure, stale evidence, unsupported lowering, warning-phase
controls, and artifact drift each produce a stable rejection code. Trusted
boundaries and approved external TCB outcomes require an explicit bounded-TCB
manifest. The proposed release command has a strict SDN ingestion boundary. Its
bundle schema contains complete typed evidence, the declared payload hash,
signer identity, public key, and signature; a separate policy schema contains
approved signer-to-public-key-hash bindings. Unknown or duplicate fields,
missing values, incorrect byte widths, and bytes outside `0..255` fail before
cryptographic evaluation.
The evidence hash includes `delivery_gate_manifest_hash`; the loader recomputes
that manifest from all eight ordered gate records. Consequently, changing a
gate status, receipt identity, evidence hash, diagnostic, or order invalidates
admission even when the structural delivery reducer would otherwise pass.
All release-security identities use SHA-256 with length-prefixed canonical
fields. The general assurance polynomial checksum is not accepted as a
cryptographic evidence identity. Every passed-gate receipt hash must also have
exactly one file at `build/verification/release-receipts/<sha256>.receipt`; the
planned CLI recomputes its SHA-256 before admission, and rejects absent, extra,
duplicate, or changed receipt material.
V2 materialized receipts additionally begin with the `FormalDeliveryReceipt-v2`
envelope and name their exact formal gate; opaque or cross-gate content is
rejected. The final gate `evidence_hash` would remain in the signed gate row rather
than inside each receipt, because that hash is derived from the receipt hashes
and embedding it in the receipts would create a circular identity. Each
planned collector's typed receipt schema binds its semantic evidence before
producing the signed gate row. The planned
`finalize_formal_gate_collection_v2` is the only
collector-to-release finalizer: it validates raw receipt bytes, puts their
payload hash and collector-local semantic evidence hash in the envelope, and
then derives the release-facing receipt and gate identities from those bytes.
The SHA-256 migration applies at the evidence source: `VerificationCacheKeyV1`,
`ProofReceiptV1`, compiler certificates, weave manifests, replay-checker
receipts, and independent replay closures emit SHA-256 identities over
length-framed canonical records. Release code does not legitimize a weak
upstream checksum by wrapping it in another hash.

Planned Gate 0 (`verification_truthfulness`) has a typed collector design. For each exported
proof root it requires a unique `ProofReceiptV1`, exactly one closed transitive
axiom audit, and an accepted fresh-plus-independent replay closure bound to the
same artifact. The retained axiom report is re-audited against the exact proof
root and artifact rather than trusting a caller-built audit summary. The full
`VerificationCacheKeyV1` is checked against the receipt, binding Lean,
Mathlib, solvers, tactic policy, target, profile, and semantic inputs. It
publishes a passed delivery record only together with exact
materialized receipt content; rejected axioms, weak identities, replay drift,
unproven statuses, or duplicate roots produce a failed gate with no passing
receipt hashes.

The planned V2 release loader independently parses each `FormalDeliveryReceipt-v2`
envelope rather than accepting a prefix or substring. Its four canonical header
lines bind exactly one formal gate, one collector semantic-evidence SHA-256,
and the SHA-256 of the retained raw payload. All envelopes for a passed gate
must agree on the semantic identity, and the loader recomputes that gate's
`FormalDeliveryGateEvidence-v2` hash from the sorted materialized envelope
hashes. Payload, semantic, duplicate-field, cross-gate, and gate-evidence
substitution fail admission even if a signed outer bundle retains hash-shaped
strings.

Planned Gate 1 (`exact_core_semantics`) consumes a self-validating canonical VIR module:
every reachable function, type, provenance edge, effect closure, and module
identity is recomputed with framed SHA-256. Only `SemanticClass.Exact` types
are accepted in this gate. Five executed check receipts are mandatory in a
frozen order: typed Lean lowering, unsupported-negative cases, generated
fallback scanning, fixed-width integer edges, and `Result` outcome separation.
Each receipt binds the VIR hash, tool identity, command policy, retained output,
outcome, and diagnostic. Missing, reordered, stale, output-free, timed-out, or
failed checks produce a failed gate; no caller-authored aggregate pass boolean
exists.

Planned Gate 2 (`vir_compiler_relation`) starts with an executed construction receipt
that binds the exact canonical woven-program hash to the self-validating VIR
hash, generator identity, command policy, and retained output. It then requires
one executed validator receipt per `CompilerCertificateV1`. Certificate edges
must form a gap-free ordered chain from the VIR semantic hash to the exact
artifact SHA-256; every certificate payload and validator result is
materialized separately. A stale construction, woven drift, missing validator,
certificate reorder/gap, timeout, missing output, or final-artifact mismatch
fails without passing evidence.

Planned Gate 3 (`aop_macro_closure`) checks the exact `WeaveManifestV1` against the
same self-validating VIR: base source, macro expansion, woven identity, resolved
join-point SymbolIds, and introduced symbols must all occur in canonical
provenance/closure. Every resolved advice ID has exactly one ghost or bounded
runtime-monitor certificate; behavior-changing advice is rejected in verified
v1. Each certificate's proof hash must resolve to exactly one materialized
Gate 0 truthfulness receipt. An executed weaver receipt binds tool/policy,
retained output, introduced-symbol closure, and a derived lock preventing
post-proof dynamic transformation. Pointcut drift, missing introduced symbols,
unmatched/duplicate advice, absent proof material, or an invalid lock fails.

Planned Gate 4 (`simpleos_vertical_slice`) consumes seven frozen subsystem classes in
order: capability authority, scheduler lifecycle, bounded IPC, shared memory,
process wait, process queue, and crash-safe storage. The product adapter accepts
only implementation-linked receipts at `source_refined`; each would be
bound to its exact SHA-256 source/model semantics, canonical source receipt,
proof receipt, verified cache key, closed trust manifest, transitive axiom
report, and same-artifact fresh/independent replay. Missing, reordered,
duplicated, model-only, stale, weak-hash, artifact-drifted, or open-trust input
fails without receipt material. The collector emits two receipts per subsystem
plus one aggregate receipt; it cannot promote a model proof itself.

Planned Gate 5 (`generated_rv32i_end_to_end`) composes the proposed generated
RV32 ADD product protocol. It requires executed SBY proof, reachability cover, and
killed-mutant evidence at `model_proven`; an independently checked HWIR-to-RTL
compiler certificate; RTL-to-netlist equivalence at `backend_refined`; and the
pinned independent Sail ADD witness at `model_proven`. All lanes must bind the
same HWIR, RTL, RVFI contract, and assumption-manifest SHA-256 identities, and
the equivalence lane must name a synthesized netlist. Every referenced tool
output, version, trace, receipt, and certificate is materialized by exact hash;
specified-only jobs, scope gaps, missing outputs, identity drift, weak hashes,
or unrelated compiler edges fail without passing evidence.

Planned Gate 6 (`rv64_privilege_mmu_linux`) freezes seven ordered checks over one exact
RV64 product identity: shared-XLEN refinement, privilege/CSR proof, MMU/page-walk
proof, precise trap/interrupt proof, post-synthesis equivalence, Linux boot, and
architectural compatibility validation. The first four require materialized
kernel-replayed proof identities, synthesis requires an independently checked
refinement certificate, and the final two are explicitly classified as
executed validations—not theorem proofs. Every check binds the same HWIR, RTL,
netlist, OS image, platform profile, and assumption manifest; tool/policy and
distinct retained output are materialized. Missing/reordered checks, product
drift, timeout, proof substitution, or a validation that impersonates a proof
fails closed. This protocol does not claim that the presently missing RV64
product evidence exists.

Planned Gate 7 (`verified_release`) is collected before the eight-gate manifest is
sealed. It requires an `artifact_verified` reachable closure, accepted tool
outcomes, zero unsupported/stale/warning/environment counts, and unique
materialized proof, compiler-certificate, trust, replay, mutation, non-vacuity,
and optional bounded-TCB receipts. It emits a pre-manifest closure receipt;
required material already owned by predecessor gates is resolved exactly once
but not republished, while only genuinely new material becomes Gate 7 receipt
ownership. This preserves the release loader's global no-duplicate invariant.
The caller would then insert all eight gate rows, recompute the canonical
manifest, and sign the complete release evidence. The planned release CLI
additionally hashes
the actual artifact at
`build/verification/release-artifacts/<signed-sha256>.artifact` through the
canonical file facade and requires that observed hash to equal both signed
artifact identities. Matching hash strings without matching deployed bytes can
no longer admit a release.

The planned `validate_signed_verified_release_bundle_v1` additionally binds the exact
evidence payload hash, signer, approved-signer policy, signature-verifier
identity/evidence, and passed release decision. Its typed signature receipt is
a protocol boundary for callers. The proposed `app.verify.release_signature`
adapter invokes the
pure-Simple RFC 8032 Ed25519 owner over the canonical evidence-hash bytes and
constructs the receipt from the actual verification result. `simple verify
release BUNDLE.sdn` reconstructs the evidence and loads approved keys only from
the fixed repository policy `config/formal/verified_release_signers.sdn`. It
then calls the cryptographic adapter and compiler-owned signed-bundle reducer.
The caller cannot substitute a policy path, and the bundle schema has no
admission boolean; an injected `verified: true` is rejected as unknown.
The signer policy file is absent on current main. Release therefore remains
blocked; when introduced it starts deny-all until an authorized change adds a
reviewed public-key hash. Private keys never belong in the repository.
`ApprovedReleaseSignerV1` binds the signer name to the exact public-key hash;
reusing an approved name with another key is rejected even when that other key
produces a cryptographically valid signature.

The planned `evaluate_formal_delivery_gates_v1` consumes exactly eight ordered gate
records. A passed record requires nonempty unique receipt identities, an exact
evidence hash, and no diagnostic. A failed or blocked record requires a reason
and cannot publish passing evidence. Any later pass is premature; a release
decision on a partial plan is also rejected. Eight passing gates plus an
admitted legacy `SignedVerifiedReleaseBundleDecisionV1` can produce only the
legacy delivery result. A typed `verified` release additionally requires the
V2 policy-bound reducer and its strict V2 SDN parser/admission entry point. The
delivery reducer derives the bundle hash internally.

At module scope, direct MIR calls resolve against unique internal function
names and become exact callee SymbolIds before the monotone effect fixed point.
A caller therefore inherits effects derived from the callee's actual MIR, not
from name prefixes. Duplicate internal names, unknown direct targets, indirect
calls, and absent callees fail closed.

The proposed canonical Lean backend includes a first effectful subset for one
straight-line block of homogeneous exact global state. It emits the source
function as an explicit state transformer
`(Nat → α) → args → result × (Nat → α)`, lowers ordered global loads and stores
against the threaded state, and generates an actual-function frame theorem for
every region outside the manifest write set. Lean 4.33 accepts the generated
theorem with only standard `propext`/`Quot.sound`. Mixed global value types,
control-flow blocks, effectful source contracts, and non-global effects fail
closed; they are not coerced into this subset.

The Result ABI validation edge observes both logical variants and their tagged
runtime projections, rejecting enum-identity, discriminant, payload, or
one-sided-coverage mutations. Its certificate identity includes the exact
runtime artifact hash, exact `ResultTaggedAbi.validate_sound` proof root,
transitive axiom audit, and independent-check result; the validator alone does
not assert that an unproved runtime implements
`rt_enum_new`.

## Lean and solver design

Typed `LeanTypeIR`, `LeanTermIR`, `LeanPatternIR`, `LeanBinderIR`, `LeanDefinitionIR`, `LeanTheoremIR`, and `LeanProofReferenceIR` are validated before printing. A deterministic VC classifier routes definitional, linear, polynomial, bit-vector, finite, inductive, state-machine, heap, concurrency, floating-point, temporal, and boundary goals. Every external result is `proved_with_replayable_certificate`, `proved_by_approved_external_tcb`, `counterexample`, `unknown`, `timeout`, or `tool_failure`.

The proposed release audit would run normal Lean checking, transitive axiom
inspection, fresh checking, and configured independent replay.
Tool/import/tactic/simplifier identities would be cache inputs.

## Caching and scheduling

The proposed scheduler would operate on SymbolId SCCs. A semantic cache hit
would require exact `VerificationCacheKey v1` equality. Changed pointcut
matches, layout, dependency theorem, solver policy, compiler pass, target, or
trust policy would invalidate dependents. Planned observability reports
classification time, engine time, cache hits/misses, invalidation cause, proof
DAG critical path, and max RSS.

## Product flows

### SimpleOS

The proposed initial slice would expose typed kernel events for capability
lookup/revoke, task state changes, IPC enqueue/dequeue/close/cancel, map/unmap,
and storage prepare/commit/recover. A planned bounded explorer would emit
source-mapped counterexample traces. General invariants and abstract-to-VIR
refinement would remain Lean proof roots. Environmental predicates could
generate bounded fail-stop monitor aspects before VIR.

### RISC-V

The planned HWIR defines `RiscvRetireRecord`; generated RVFI would be a checked
projection. Receipts bind CoreConfig/XLEN/extensions, Sail version, RTL,
property set, cover witnesses, SBY engine, and netlist. Delivery is planned to
begin with one RV32I instruction family, then expand by the staged gates.

For the planned first ADD slice, `run-fv2-rv32-add-equivalence.shs` would consume only the
already executed formal bundle. It rejects a stale RTL hash, duplicate or
preexisting equivalence fields, missing tools, failed equivalence, and missing
netlist. Its policy identity is the hash of
`ghdl-vhdl2008|prep-top|equiv-opt-assert-synth-top|synth-top|write-json`.
`reduce_rv32_add_external_equivalence_receipt_v1` requires the formal receipt
and every equivalence identity before returning `backend_refined`; malformed,
cross-module, stale, or failed inputs return `failed`.

The planned `run-fv2-rv32-add-sail.shs` owns the independent concrete oracle witness. It
requires `SAIL_RISCV_SIM`, `SAIL_RISCV_RV32_CONFIG`, and `SAIL_RISCV_LOCK`.
The lock must bind the approved repository/revision to the exact simulator and
configuration hashes; the runner rehashes both before use. It then compiles the
tracked RV32I probe; checks exact ADD encoding `002081b3`; runs four Sail
instructions; and requires x3/gp to become 12. Absent model/config returns 2.
The parser rejects wrong revision, result, module, HWIR/RTL, or malformed
artifact identities and caps this bounded witness at `model_proven`.

## Diagnostics

All failures carry stable diagnostic code, status, obligation/certificate ID, source span/SymbolId, semantic hash, engine outcome, and minimal mapped trace when present. Reports explicitly say “model proven; implementation refinement absent” where applicable.

## Migration

Existing Lean projects are inventoried as abstract models and mapped to candidate implementation roots. Existing `verified` states are translated conservatively to `model_proven` unless a checked source and backend refinement already exists. No old receipt is upgraded by label alone.
