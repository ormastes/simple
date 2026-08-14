<!-- codex-design -->
# Simple Formal Verification 2.0 Architecture

**Status:** Implemented FV2 capsule in this working tree; executable admission remains blocked
**Date:** 2026-08-14
**Requirements:** `doc/02_requirements/feature/simple_formal_verification_2_0.md`

## Normative scope and current-tree truth

This document is the accepted FV2 architecture. Normative verbs
(`must`, `requires`, `owns`, and `rejects`) specify the intended architecture;
they do not assert that a named type, collector, reducer, runner, CLI, or script
exists. An item is implemented only when the current-tree status tables below
say so. The restored capsule now supplies the frozen interfaces, VIR,
obligations, collectors, replay/release adapters, and bounded product runners;
their executable admission remains blocked on the canonical Stage 4 runtime.

The pre-existing typed MIR evidence bridge remains the execution foundation:
`DecisionProbe` and `ConditionProbe`, JSON retention, optimizer/visitor
preservation, fail-closed admission, and explicit interpreter/LLVM rejection.
This bridge transports evidence identity and liveness; it neither lowers probes
to runtime evidence nor promotes any formal status.

## Frozen integration contract

The ten display names are frozen exactly as shown below. Code must use the one
mapped identifier; alternative casing, acronym spelling, aliases, or
near-equivalent records do not satisfy the boundary.

| Frozen display name | Planned Simple code identifier |
|---|---|
| `VerificationIR v1` | `VerificationIrV1` |
| `SemanticCoverage v1` | `SemanticCoverageV1` |
| `ProofObligation v1` | `ProofObligationV1` |
| `ProofReceipt v1` | `ProofReceiptV1` |
| `TrustManifest v1` | `TrustManifestV1` |
| `WeaveManifest v1` | `WeaveManifestV1` |
| `CompilerCertificate v1` | `CompilerCertificateV1` |
| `HardwareProofReceipt v1` | `HardwareProofReceiptV1` |
| `FormalStatus v1` | `FormalStatusV1` |
| `VerificationCacheKey v1` | `VerificationCacheKeyV1` |

All ten identifiers now exist in the working tree. A shape change requires a
new version, migration, and stale-cache rejection evidence.

The executable/manual flow is likewise frozen to these visible steps:

1. `step("Audit the formal claim boundary")`
2. `step("Construct canonical verification evidence")`
3. `step("Reject stale or unsupported evidence")`
4. `step("Replay the shipped artifact independently")`

The only shared setup/checker helper names are `setup_fv2_fixture`,
`check_fv2_gate`, and `check_fv2_replay`. An incomplete helper calls
`fail(...)`; it must never return a placeholder success or silently no-op.

Current admission remains blocked. The canonical Stage 4 pure-Simple CLI is
absent in this detached worktree; the available fallback artifact fails the
bounded `test --help` ABI probe, so Rust-seed, wrapper, and static-only results
cannot close executable criteria. Backend closure is also incomplete until
every MIR consumer handles `DecisionProbe` and `ConditionProbe` explicitly and
the native x86_64, AArch64, RV32, and RV64 selectors are proven to reject an
unlowered probe rather than reaching wildcard NOP behavior. These are blockers,
not approved trust boundaries.

## Decision

Simple adopts a closed evidence chain:

```text
source -> typed/effect-checked HIR -> expanded+woven HIR -> VIR
       -> validated lower IR -> binary/OS image or RTL -> netlist/deployed artifact
```

Each edge owns exactly one evidence class: universal refinement proof, checked per-build certificate, approved trust boundary, or verified assumption monitor. A model theorem without a checked edge to implementation is `model_proven`, never `artifact_verified`.

## Assurance-policy version boundary

This section is normative and blocked: the named V2 types and consumers below
are not present on current main. `ResolvedAssurancePolicyV1` remains the
compatibility boundary. The planned `verified` tier will be represented only
by `AssuranceStrictnessV2` and `ResolvedAssurancePolicyV2`, whose `APOLV2-*`
hash must be distinct from every V1
policy hash. This prevents an older tool from reading a V2 profile as an
unrecognised permissive value. Planned lint, driver, interpreter, run, and
test projections may accept the `verified` spelling while enforcing it as `critical`;
they cannot produce an artifact-verification claim. Only V2-aware FV2
receipt/release code may consume `verified`, and it must retain the V2 policy
identity in its evidence closure.
The planned `CompileContext` integration will carry that V2 identity alongside
its frozen V1 projection and disable dynamic runtime AOP whenever the V2 strictness is `verified`, so a
runtime registration cannot become an untracked post-VIR transformation.
The current driver weave and debug-trace passes are post-MIR transformations.
Verified compilation therefore rejects advice/log weaving and debug trace
injection at that boundary until the canonical pre-VIR weaving path produces
the required manifest and refinement evidence.

The planned `SignedVerifiedReleaseBundleV2` will be the typed admission reducer; its payload
hash includes both the frozen V1 evidence record and the V2 policy hash.
The SDN loader must expose a separate strict V2 bundle parser/admission path which
requires the canonical resolved policy in the signed input. V1 remains a
compatibility representation and cannot authorize a typed `verified` release.
The planned release CLI must detect the V2 schema before any compatibility parsing and
never falls a V2-marked document back to the V1 reducer.

## Pattern evaluation

| Pattern | Decision | Reason |
|---|---|---|
| Direct syntax-to-Lean generation | Reject | Cannot establish typed semantic coverage or common proof/execution identity. |
| Handwritten shadow models as implementation proof | Reject | Manual translation can diverge; retain them as abstract specifications. |
| Whole-compiler proof first | Defer | Multi-backend scope is too large for the first closure. |
| Typed VIR plus translation validation | Adopt | Establishes a tractable, per-artifact refinement chain and can evolve into universal pass proofs. |
| RVFI-only CPU assurance | Reject as sufficient | Checks architectural retirement, not HWIR generator or synthesis correctness. |

## Layer ownership

Every capsule in this section is planned unless the current-tree table marks a
foundation implemented. The bullets define ownership, not present deployment.

1. **Canonicalization capsule:** parser/name/type/effect owners expand macros, resolve exact join points, deterministically weave, and emit one immutable canonical HIR.
2. **VIR capsule:** translates canonical HIR into executable formal semantics and rejects uncovered constructs.
3. **Obligation capsule:** classifies and emits an exact thirteen-kind,
   engine-neutral DAG. Dependencies must precede consumers, all edges remain
   inside the closure, and the sole final root is `trust_closure`; proposition
   identities are typed inputs and missing identities fail closed.
   The canonical MIR adapter does not accept those identities from callers: it
   derives the initial acyclic-CFG/self-recursive subset from retained typed
   contracts, exact VIR-ready representations, serialized execution,
   region/effect ownership, call closure, backend policy, and closed trust.
   Module composition resolves direct names to unique SymbolIds and retained
   contracts. Its first admitted call edge targets a pure, nonrecursive leaf;
   unresolved, indirect, effectful, or recursive components fail closed until
   transitive region/SCC proof composition is implemented.
4. **Engine adapters:** Lean, certified SMT/SAT, bounded model checking, and hardware engines return typed results; adapters cannot reinterpret `unknown` as success.
5. **Refinement capsule:** checks pass-level or build-level source/VIR/target relations.
6. **Evidence capsule:** constructs receipts, trust manifests, dependency DAGs, cache keys, and final closure status.
   Planned `VerifiedReleaseEvidenceV1` supplies the evidence closure, while
   planned `VerifiedReleaseEvidenceV2` binds that closure to a V2 policy. Artifact and
   evidence hashes must match, every reachable status must be artifact-verified
   or explicitly bounded-TCB, and every non-proof tool/staleness/unsupported or
   environment state produces a named rejection code.
7. **Product capsules:** SimpleOS and RISC-V specialize target semantics without bypassing common evidence interfaces.

The planned `FormalDeliveryGateV1` will freeze the release sequence: truthfulness, exact core
semantics, VIR/compiler relation, AOP/macro closure, SimpleOS vertical slice,
generated RV32I, RV64/privilege/MMU/Linux, then verified release. A later gate
cannot pass after any blocked/failed predecessor, and the final gate cannot
become release-ready without a typed, internally passed release decision. A
V1 decision is compatible with legacy evidence collection; a typed `verified`
release additionally requires `SignedVerifiedReleaseBundleDecisionV2`. A
caller-authored decision or hash is not an accepted input.

These are MDSOC virtual capsules: verification policy cross-cuts compiler, OS, hardware, and build modules, while semantic ownership remains with each producing layer. Feature transforms may add proof/monitor material only before VIR. The AOP/macro closure receipt binds an explicitly empty post-VIR transform sequence; any later compiler transformation belongs to the separately checked VIR/compiler-relation chain, never to an unrecorded weave step.

### Planned typed state and effectful contracts

For the admitted typed-global subset, one MIR region manifest owns effects,
state shape, transition identity, and frame identity. Module-level direct calls
resolve to unique internal `SymbolId`s and inherit those effects in deterministic
symbol order. Canonical module VIR consumes that closure, records exact callee
`SymbolId`s, and binds the closure hash into the module semantic identity.
Argument/result contracts quantify the actual generated state transformer and
inspect its returned outcome/state pair. An effectful invariant reuses existing
ghost-call syntax: its zero-argument predicate must resolve by retained HIR
`SymbolId` and name to one exact MIR function, return `bool`, and have closed
read-only typed-global effects. The generated initialization/preservation
theorems apply that actual predicate function to the explicit pre/post state.
Argument-only predicates, name-only matches, writes, missing targets, and
non-Boolean predicates fail closed.
The owner obligations must include a planned `StatePredicateBindingV1` hash covering the
predicate MIR execution and region manifest. Promotion to `source_refined`
requires exact namespace-qualified generated theorem roots plus artifact,
cache, axiom-audit, trust-manifest, and independent-replay identities.
The planned release-facing obligation entrypoint must derive input, reachability,
transition, frame, recursive-call, and well-founded-order identities from
canonical MIR; caller-assembled semantic contexts are diagnostic APIs only.
Where legacy MIR direct calls still carry a textual operand, the planned resolver must emit
`ResolvedDirectCallManifestV1`. Each entry binds an exact serialized call site,
owner and callee SymbolIds, callee signature/body identities, exact module
snapshot, and resolver receipt. The planned `ResolvedCanonicalModuleClosureV2` requires
that manifest before exposing a module closure; missing, stale, extra, or
text/signature-mismatched bindings fail closed. This is a compatibility bridge,
not a weaker name lookup, until resolved callee identity becomes native MIR.
The planned `ResolvedVerificationIrModuleV2` must consume the same validated manifest for its
transitive typed effect closure and called-SymbolId list, then binds the
manifest hash into its semantic identity. Thus a proof cannot use one call
closure while compilation/VIR presents another.

The planned Lean CLI checker must report successful checked models as `model_proven`, not
`verified`. It retains Lean output, requires an explicit transitive
`#print axioms` root for every declared theorem/lemma, and rejects missing
roots, `sorryAx`, `Lean.trustCompiler`, and undeclared project axioms. A normal
Lean exit code alone is never proof evidence.

Fresh replay and independent replay are planned separate receipt classes. A
validated pinned `leanchecker --fresh` lane may supply fresh Lean-kernel replay; it cannot
satisfy the independent-kernel slot. `IndependentReplayClosureV1` requires an
accepted fresh receipt and an accepted independent-implementation receipt over
the identical module, declaration root, and artifact hash. Missing output, timeout, rejection,
tool failure, class substitution, and artifact drift fail closed.
The planned `ReplayRunnerConfigV1` must separate the launcher path from the checker path, so a
fresh receipt hashes the actual `leanchecker` binary rather than Lake. The
planned runner must use argv-preserving process execution, validate canonical module
names, retains output, and classifies timeout/tool/rejection outcomes. The
fresh checker is silent on success, so the receipt owner records a deterministic
success attestation bound to checker hash, module, artifact, and exit zero;
that exception never applies to the independent checker class. The
planned independent lane must accept only a pinned, hashed adapter that owns the exact
format-v2 `lean4export` fork-to-`nanoda` pipeline with transitive
use of `sorryAx` disabled. The adapter exports an exact declaration root rather
than the whole module environment.
The replay schema is owned by `compiler.common.assurance`, not the tool layer.
Both `source_refined` obligation promotion and `artifact_verified` release
promotion receive an `IndependentReplayClosureV1` value and verify its exact
hash and artifact identity. An opaque nonempty replay string is insufficient.
The repository adapter deliberately differs from the general-purpose official
CI defaults: it omits `Lean.trustCompiler` and `sorryAx`, excludes unpermitted
axioms from the independent environment so any transitive use fails checking,
and disables nanoda's native Nat/String extensions in the closed lane. Merely
declaring an unused axiom in an imported environment is not confused with a
proof-root dependency. Provisioning pins reviewed lean4export/nanoda commits,
proves their format compatibility, and is itself gated on a genuine
pure-Simple compiler.

The closed independent lane has a deliberate capability boundary: nanoda with
Nat/String extensions disabled rejects roots containing Lean primitive
literals (`#ELN`/`#ELS`). Gate orchestration records those as replay-rejected
and never silently enables the extensions. A future bounded-TCB profile may
admit independently reviewed primitive-literal rules, but that evidence cannot
be relabeled as closed verification.

`BoundedNatNormalizerReceiptV1` is a planned, non-promoting candidate schema
for a future independently checked, bounded export normalizer. It records exact
input/output export hashes, tool identity, finite literal/rewrite bounds, and
an explicit `native_extensions_enabled = false` condition. It has no conversion
to an independent replay closure: a later implementation must still submit the
normalized export to the pinned independent checker and prove its transformation
relation before any replay receipt can be considered.

## Frozen interfaces v1

| Interface | Required contents |
|---|---|
| `VerificationIR v1` | Symbol/source IDs, exact representation, effects, capabilities, contracts, transitions, calls, trust refs, semantic class. |
| `SemanticCoverage v1` | Construct variant and exact/abstract-refined/external-contract/unsupported status with lowering and negative-test ownership. |
| `ProofObligation v1` | Stable ID, proposition class, semantic inputs, dependencies, source mapping, engine policy, expected result class. |
| `ProofReceipt v1` | Exact declaration roots, dependency closure, axioms/trust, tool versions, policies, hashes, replay result. Fresh and independent replay receipts must name the identical root. |
| `TrustManifest v1` | Logic/kernel, project axiom, native evaluator, solver, FFI/assembly, hardware/environment, fairness/memory-model assumptions. |
| `WeaveManifest v1` | Ordered exact join points, advice/proceed policy, introduced symbols, expansion and weave hashes. |
| `CompilerCertificate v1` | Before/after semantic identities, relation, validator/checker identity, certificate, counterexample or failure. |
| `HardwareProofReceipt v1` | HWIR/RTL/netlist hashes, ISA/config identity, assertions, covers, assumptions, engines, equivalence results. |
| `FormalStatus v1` | `not_checked`, `specified`, `model_proven`, `source_refined`, `backend_refined`, `artifact_verified`, `trusted_boundary`, `admitted_development`, `unsupported`, `failed`, `stale`. |
| `VerificationCacheKey v1` | VIR/contract/weave/macro/dependency hashes, semantic versions, target, tools, tactics, solver and trust policy. |

All interfaces use versioned canonical serialization. No wildcard/default construct coverage is permitted in `verified`.
The v1 freeze begins with the exact-root field present; no earlier locally
generated receipt lacking that field is admissible or migratable.

## Semantics and refinement

`SourceStep`, `VIRStep`, and target-specific transition relations expose observable event traces. The default obligation is behavior inclusion:

```text
VIRBehavior    subset-of SourceBehavior
TargetBehavior subset-of VIRBehavior
```

Deterministic fully defined code may require observational equality. Optimizations require after-pass behavior to be included in before-pass behavior. Contract VCs quantify over actual `Exec(function, pre_state, args)` outcomes and split `Ok` from `Err` postconditions.

## Verified closure

Closure begins at verified package/artifact roots and includes transitive callees, types, trait implementations, generated helpers, macros, aspects, proof imports, compiler passes, backend/runtime support, and linked objects. Private visibility does not exempt a dependency. Every node terminates in verified evidence or a policy-approved bounded trust entry.

## AOP and macro boundary

Expansion and weaving precede VIR. Wildcards resolve to ordered SymbolId sets recorded in `WeaveManifest`. The execution receipt hashes the exact manifest, VIR identity, and an empty `PostVirTransformSequence-v1`; a nonempty or substituted sequence rejects the AOP/macro gate. Ghost aspects require observational noninterference; runtime monitors are included in VIR and fail explicitly; behavior-changing aspects are initially unsupported. Around continuations are modeled as affine/linear capabilities with declared proceed multiplicity.

## SimpleOS specialization

Existing Lean models become abstract specifications. Contextual refinement connects them to a first vertical VIR-backed slice: capability/object table, process lifecycle, one bounded IPC channel, scheduler lifecycle, one map/unmap operation, and one transactional recovery path. Bounded interleaving exploration finds traces; Lean proves invariant/refinement closure. Interrupt, DMA, MMU/TLB, timing, device, and persistence assumptions enter `TrustManifest` and gain boot/runtime monitors where feasible.

An `AspectCertificateV1.BoundedRuntimeMonitor` alone is not monitor evidence for
a verified gate: its frozen shape has no environmental-predicate identity,
artifact binding, or fail-stop policy. The AOP gate therefore rejects it rather
than accidentally promoting an unbound or fail-open monitor.
The planned `RuntimeAssumptionMonitorReceiptV1` will define that dedicated receipt shape:
assumption, exact VIR/artifact, monitor binary, proof receipt, positive bound,
and explicit fail-stop outcome. The planned `runtime_assumption_monitor_binding_diagnostic_v1`
will be the deliberately non-promoting materialization adapter: it must reject a receipt
unless the artifact producer supplies the exact VIR and artifact hashes, exact
woven advice identity, sorted declared assumption set, and exactly one matching
proof-receipt file. It does not alter the frozen AOP collector: legacy
`BoundedRuntimeMonitor` certificates remain rejected. Gate integration remains
fail-closed until a runtime producer calls the adapter from an artifact-aware
delivery gate; environmental assumptions remain bounded-TCB evidence, not
closed `artifact_verified` evidence.

Retained axiom output alone never promotes a SimpleOS slice. It can establish
`model_proven` after exact-root auditing. `source_refined` additionally requires
a typed `ProofReceiptV1`, accepted `IndependentReplayClosureV1`, exact artifact
identity, and dependencies on the product/model semantic hashes. The proposed
bounded capability-rights, bounded scheduler-completion, exact channel-close,
DBFS commit, and one-page shared-unmap slices must implement this promotion
shape. The planned scheduler proof uses one composite Lean release root covering
done-state, first-write-wins, exact non-done record, and park-reason clearing.
Channel close/drain similarly composes exact output, channel idempotence, and
exactly-once wake behavior. DBFS commit composes WAL-before-visible,
successful recovery visibility, failed-unflushed invisibility, and crash
atomicity. One-page shared unmap composes survivor-reference preservation,
dirty last-reference writeback/retirement, private-map framing, and repeated
unmap idempotence. Constructed replay records exercise protocol
only; an executed independent replay remains required for release evidence.

The proposed process-lifecycle slice must target the actual scheduler transition chain, not
the older runtime-oriented shadow model: a live child wait blocks, exit
publishes the zombie/status and wakes the parent, collection returns that exact
status and removes the child, and a second collection reports no child. Its
separate exact Lean bridge deliberately excludes orphan adoption until a
canonical Simple owner is linked.

The proposed process-queue slice must execute the fixed-capacity kernel queue directly. It
binds FIFO payload order, attached-handle identity, full-queue `EAGAIN`,
send-close drain-to-EOF, post-close `EPIPE`, and generation-based stale-handle
rejection. Its Lean bridge proves the general FIFO/backpressure/close core;
generation identity remains checked against the concrete table implementation.

## RISC-V specialization

One XLEN-parametric HWIR owns state, decode/execute, reset, traps, and architectural retirement. RVFI is generated as a projection of the same retirement transition. Sail is the independent ISA authority; riscv-formal/SBY checks retirement; a separate refinement/equivalence lane checks HWIR-to-RTL and RTL-to-netlist. Side-channel security is a distinct proof track.

Constructed formal-job objects test the proof protocol only and have status
`specified`; they cannot establish `model_proven`. Executed SBY evidence enters
through an external receipt bound to the exact module, HWIR, RTL, RVFI
contract, assumptions, generated core/harness/jobs, engine identities, proof
output, cover output, and killed-mutant counterexample. The pure-Simple bundle
generator and planned `check-fv2-rv32-add-end-to-end.shs` will own generation and execution;
the latter rejects a seed compiler before producing evidence. Existing pinned
Sail Zca tables remain classification-only and never imply ADD equivalence.

The proposed ADD lane requires a separate executed RTL-to-netlist edge. Its
planned runner will use GHDL to elaborate
the generated VHDL-2008 RVFI top; Yosys snapshots that design, runs the exact
`synth -top` transformation under `equiv_opt -assert`, repeats that same
transformation to retain a JSON netlist, and record RTL, netlist, proof-log,
tool-version, module, and command-policy hashes. The planned external receipt
reducer must revalidate the complete SBY proof/cover/mutant closure and promote only the
exact combined evidence to `backend_refined`. It never grants
`artifact_verified`: Sail ISA comparison and deployed-artifact identity remain
open gates.

The independent ISA lane is a separate receipt. It compiles a fixed RV32I ELF
containing opcode `002081b3`, executes four instructions with the Sail model at
the approved `a33475a…` revision and an explicit RV32 configuration, and
requires the architectural trace to write 12 to x3. The receipt binds the
repository/revision, simulator/config, probe source/ELF/disassembly, trace,
run output, HWIR, and RTL identities. This one concrete differential witness is
`model_proven`, not a universal ISA proof. Missing Sail executable or RV32
configuration is `blocked` (exit 2), never pass.

## Security and failure behavior

- `sorry`, `admit`, undeclared axioms, unapproved `Lean.trustCompiler`, stale inputs, timeout, unknown, missing tools, and checker disagreement block closure.
- Each implication/invariant/property family has a satisfiable/reachable witness.
- Non-equivalent surviving mutations block the affected assurance claim.
- Dynamic plugins cannot lower the host profile and must present compatible signed receipts or become explicit TCB entries.
- Verified release ingestion is specified as two strict SDN schemas: an
  evidence/signature bundle and a repository-pinned signer/key-hash policy.
  The planned loader must reconstruct V1 compatibility evidence and V2 policy-bound
  evidence through distinct entry points. Both paths reject unknown or
  duplicate fields and never accept a serialized release-admission flag.
  A canonical hash of all eight ordered delivery gates is itself part of the
  signed evidence, closing substitution between signature and gate reduction.
  Security identities are length-framed SHA-256 values. Passed-gate receipt
  hashes are materialized and rehashed from a fixed build evidence directory;
  caller-selected receipt paths are outside the interface.

## Compatibility

This architecture supersedes the six-state claim model in `doc/04_architecture/infra/misc/lean_verification_contract.md` for Formal Verification 2.0 artifacts. Existing projects retain `model_proven` value during migration. The current fail-closed RISC-V placeholder gate remains authoritative until real generated RTL satisfies it.

## Current-tree artifact status

| Architecture artifact or surface | Intended owner | Current-tree artifact/status |
|---|---|---|
| MIR probe opcodes and payload | `compiler.mir` | **Implemented foundation:** `src/compiler/50.mir/mir_instruction_kinds.spl` |
| MIR probe serialization | `compiler.mir` | **Implemented foundation:** `src/compiler/50.mir/mir_json.spl` |
| Probe validation/unlowered admission | `compiler.mir` | **Implemented foundation:** `src/compiler/50.mir/mir_coverage_probe_admission.spl` |
| Optimizer, visitor, SSA, inline, DCE preservation | `compiler.mir_opt` | **Implemented foundation:** explicit probe handling; executable closure remains gated |
| Interpreter and LLVM rejection | `compiler.interp`, LLVM backends | **Implemented foundation:** explicit fail-closed arms |
| Non-LLVM backend probe closure | C/WASM/native/GPU/VHDL backends | **Blocked:** per-backend executable rejection evidence incomplete |
| Ten frozen V1 interfaces | common assurance/VIR owners | **Implemented; runtime verification blocked** |
| V2 assurance policy and compile-context identity | common assurance + driver | **Implemented; runtime verification blocked** |
| VIR, obligation, coverage, and evidence collectors | compiler verification capsules | **Implemented; runtime verification blocked** |
| Release bundle parser/reducer and delivery gate | release assurance owner | **Implemented; external evidence still required** |
| Fresh and independent replay runners/reducers | proof replay owner | **Implemented; tool execution blocked** |
| SimpleOS refinement/monitor receipt pipeline | SimpleOS verification capsule | **Implemented bounded slices; product closure blocked** |
| RISC-V ADD/Sail/SBY/equivalence runners | RISC-V verification capsule | **Implemented runners; external proof tools/evidence blocked** |
| Artifact-verified release | evidence/release capsule | **Blocked:** no end-to-end closure |

## Requirements-to-architecture traceability

Status values describe current main, not the normative destination.

| Requirement | Architecture section/interface/gate | Current status |
|---|---|---|
| REQ-FV2-001 | Decision; `FormalStatus v1`; Verified closure | Planned; MIR bridge does not promote status |
| REQ-FV2-002 | Assurance-policy version boundary | Planned/absent |
| REQ-FV2-003 | Canonicalization capsule; AOP and macro boundary | Planned/blocked |
| REQ-FV2-004 | Semantics and refinement; planned typed state contracts | Planned/blocked |
| REQ-FV2-005 | VIR capsule; `VerificationIR v1` | Planned/absent |
| REQ-FV2-006 | VIR capsule; `SemanticCoverage v1` | Planned; probe payload is partial foundation |
| REQ-FV2-007 | Engine adapters; typed Lean generation boundary | Planned/absent |
| REQ-FV2-008 | Obligation capsule; `ProofObligation v1` | Planned/absent |
| REQ-FV2-009 | Engine adapters; `ProofReceipt v1`; replay closure | Planned/blocked |
| REQ-FV2-010 | Evidence capsule; receipt interfaces | Planned/absent |
| REQ-FV2-011 | Canonicalization capsule; `WeaveManifest v1` | Planned/blocked |
| REQ-FV2-012 | Planned typed state and effectful contracts | Planned/blocked |
| REQ-FV2-013 | Refinement capsule; `CompilerCertificate v1` | Planned; MIR rejection is foundation only |
| REQ-FV2-014 | SimpleOS specialization | Planned/blocked |
| REQ-FV2-015 | RISC-V specialization; `HardwareProofReceipt v1` | Planned/blocked |
| REQ-FV2-016 | Security and failure behavior; mutation gates | Planned/blocked |
| REQ-FV2-017 | Verified closure; dynamic-plugin policy | Planned/blocked |
| REQ-FV2-018 | Canonicalization and compatibility boundaries | Normative constraint; no new syntax in MIR bridge |
| REQ-FV2-019 | Security and failure behavior; admission gates | Partial foundation implemented; closure blocked |
| REQ-FV2-020 | Planned `FormalDeliveryGateV1` sequence | Planned/absent |
| NFR-FV2-001 | Evidence capsule; canonical serialization/replay | Planned/blocked |
| NFR-FV2-002 | Security and failure behavior | Partial foundation implemented; closure blocked |
| NFR-FV2-003 | `TrustManifest v1`; Verified closure | Planned/absent |
| NFR-FV2-004 | `VerificationCacheKey v1`; obligation DAG | Planned/absent |
| NFR-FV2-005 | Canonicalization, VIR, evidence capsules | Planned/blocked |
| NFR-FV2-006 | Obligation scheduling and bounded monitors | Planned; no accepted measurements |
| NFR-FV2-007 | Source mapping in obligations/receipts | Planned/absent |
| NFR-FV2-008 | Frozen interfaces v1; migration rejection | Normative mapping frozen; types absent |
| NFR-FV2-009 | Independent replay; Sail authority | Planned/blocked |
| NFR-FV2-010 | Obligation DAG/cache scheduling | Planned/absent |
