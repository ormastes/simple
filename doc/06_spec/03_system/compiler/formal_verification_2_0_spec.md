# Simple Formal Verification 2.0 — Foundation Gates

> These scenarios exercise the implemented truth, profile, semantic, trust,

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 81 | 81 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Simple Formal Verification 2.0 — Foundation Gates

These scenarios exercise the implemented truth, profile, semantic, trust,

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/03_system/compiler/formal_verification_2_0_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

These scenarios exercise the implemented truth, profile, semantic, trust,
receipt, AOP-identity, and typed-Lean boundaries. They deliberately do not
claim the remaining full SimpleOS or generated RISC-V refinement gates.

Explicit compact trace for labels represented by shared scenarios:
`REQ-FV2-003` and `REQ-FV2-005` map to **Construct canonical verification
evidence**; `REQ-FV2-016` maps to **Reject stale or unsupported evidence**;
`NFR-FV2-002` through `NFR-FV2-008` map respectively to the rejection,
trust/cache, deterministic construction, measured scheduling, trace mapping,
and schema-migration checks; `NFR-FV2-009` maps to **Replay the shipped
artifact independently**. These are structural reducer fixtures until the
canonical Stage 4 runtime executes them against retained artifact material.

- REQ-FV2-001: model-only success cannot become artifact verification.
- REQ-FV2-002: verified is the fifth, raise-only assurance rung.
- REQ-FV2-004: source predicates are retained outside executable bodies with
  source maps; generated specifications quantify real argument types and call
  the emitted function; entry conditions have a separate satisfiability root;
  changing the audited proof root changes contract identity. Direct typed
  Result construction preserves payload and variant identity; propagation and
  stateful invariant/frame/termination proof closure remains pending. Their VC
  v2 identities are now fail-closed while v1 remains frozen: reachable-state, transition, region/frame,
  recursive-call, well-founded-order, and input-domain authorities are explicit
  and hashed rather than represented only by descriptive text. Canonical MIR
  currently derives input-domain, direct-recursion/order, and exact-pure
  `Unit`-state identity-transition/empty-frame identities. Pure invariants emit
  entry and actual-call exit roots plus an axiom-free frame theorem; effectful
  invariant/frame promotion remains rejected until heap/region owners land.
- REQ-FV2-006: fixed-width representations are exact in both VIR and the
  canonical MIR-to-Lean backend. Unsupported float/pointer semantics and
  signedness-dependent division/shift fail closed; checked arithmetic is never
  emitted as ordinary arithmetic with a comment.
- REQ-FV2-007: typed Lean terms reject invalid widths and proofless theorems.
- REQ-FV2-008: the engine-neutral obligation protocol emits exactly thirteen
  uniquely typed nodes in dependency order and binds semantic, invariant,
  non-vacuity, backend, and trust evidence into one final trust root. Missing
  proposition authority fails closed. The first canonical subset derives the
  complete identity set from retained typed contracts, serialized MIR,
  region/effect manifests, acyclic-CFG termination, backend policy, and closed
  trust. Unit evidence also binds one exact pure leaf callee contract into the
  owner call VC while rejecting missing contracts and hidden callee effects.
  The system fixture additionally materializes a post-MIR
  `ResolvedDirectCallManifestV1` for a caller/callee pair, verifies its exact
  SymbolId, site, signature, and body bindings, and builds
  `ResolvedVerificationIrModuleV2` from that same manifest. Removing the
  binding fails before call/effect closure, while a changed resolver receipt
  changes the V2 semantic identity. This is an adapter-level proof of
  the V2 handoff, not evidence that the production frontend emits the manifest;
  verified production compilation remains fail-closed on
  `FV2-E-CALL-MANIFEST-PRODUCER` until that producer exists.
  These scenarios do not claim transitive/effectful SCC composition or that any
  VC was executed. A separate unit-covered evidence closure structurally
  validates thirteen exact, artifact/trust/replay-bound theorem receipts with
  complete DAG dependencies, then fails on `EXECUTION-AUTHORITY`; hash-only
  fixtures no longer become `model_proven`.
- REQ-FV2-009: transitive trust reports reject hidden axioms, missing roots,
  longer-name prefix collisions against an expected theorem identity, and
  theorem declarations omitted from the explicit audit-root set. Successful
  Lean model checks report `model_proven`, never artifact verification.
  Fresh Lean-kernel replay and independent-kernel replay use distinct typed
  receipts and must agree on the exact module/artifact; two Lean checkers,
  missing output, timeout, or artifact drift cannot close the gate.
- REQ-FV2-010: semantic-key changes invalidate artifact receipts; unqualified
  release requires a closed matching trust manifest. Symbol-level scheduling
  groups recursive roots into SCCs, orders dependencies first, reports the
  critical path, and invalidates only reverse dependents.
- REQ-FV2-011: join-point/advice order changes weave identity and around advice
  requires exactly-once proceed evidence.
- REQ-FV2-012: effects retain typed regions/devices/capabilities, propagate
  through the exact SymbolId call closure, and reject unresolved indirect calls.
  Direct global loads/stores derive exact SymbolId/type/instruction manifests;
  caller-supplied VIR effects cannot contradict them, while heap pointers and
  external/device/synchronization boundaries remain explicit failures.
  The admitted homogeneous one-block global subset lowers to an explicit Lean
  state transformer and proves the actual generated function leaves every
  region outside the derived write set unchanged.
  Module-level direct calls resolve to unique internal SymbolIds and inherit
  their MIR-derived effects; canonical module VIR binds that deterministic
  closure identity and exact callees. Duplicate, missing, or indirect targets fail.
  Typed-global invariant/frame authorities derive from the same manifest, and
  effectful argument/result contracts inspect the actual generated state
  transformer outcome. Effectful invariants bind existing zero-argument ghost
  predicate calls by exact HIR/MIR SymbolId and name, require closed read-only
  state effects, and inspect the actual pre/post state. Unbound or mutating
  predicates fail closed.
  Owner VCs bind the predicate execution/region-manifest hash, and typed
  source-refinement receipts require exact generated roots and independent
  replay evidence.
  Canonical obligation generation derives all semantic authority hashes from
  MIR rather than accepting release evidence from a caller-selected context.
- REQ-FV2-013: the proved straight-line DCE subset issues a canonical compiler
  certificate for accepted elimination, rejects a changed live value, and
  rejects missing theorem-audit evidence. Result translation validation also
  checks both variants, payload bits, and enum identity and binds its
  certificate to the runtime artifact, exact proof root, axiom audit, and
  independent-check result. Full
  MIR/backend coverage remains outside this initial slice.
- REQ-FV2-017: dynamically loaded components require an exact signed receipt,
  matching verified profile/interface/compiler lineage, and discharged
  composition obligations; explicitly isolated components remain visible as a
  bounded TCB and never become closed verification.
- REQ-FV2-018: the existing `proof uses` channel expands one qualified root
  over all thirteen exact canonical VC identities. Unit evidence rejects a
  generated proof receipt that omits its expanded external dependency. Actual
  Lean emission, audit, and independent replay remain blocked evidence.
- REQ-FV2-019: the typed release reducer accepts only complete artifact-bound
  verified evidence and rejects unknown, timeout, missing-tool, tool/environment
  failure, stale, unsupported, profile-drift, warning-control, and artifact-drift
  inputs. The signed-bundle protocol binds exact payload and signer policy;
  the app adapter performs pure-Simple Ed25519 verification before constructing
  its typed receipt. Strict SDN loaders reject unknown/duplicate fields,
  malformed byte arrays, duplicate signer identities, and payload drift;
  `simple verify release` recomputes admission from the bundle and the fixed
  repository signer policy; callers cannot supply a replacement policy path.
  Release identities are SHA-256 rather than the non-cryptographic assurance
  checksum. V2 admission additionally requires the additive V3 fixed-policy
  schema, whose authority digests cover the full resolved policy, flight rules,
  and sorted signer allow list; legacy APOLV2 and V1 CLI downgrade authorization
  are fail-closed. Public constructed V3 policies remain non-authoritative until
  a trusted install-root resolver and atomic no-follow snapshot issue
  provenance. Every signed passed-gate receipt is
  rehashed from its exact fixed-root file before admission.
  Executed self-hosted test evidence remains pending.
- REQ-FV2-020: the frozen eight-stage delivery reducer preserves honest partial
  progress, rejects a pass that skips a blocked predecessor, and becomes ready
  only when every gate passes and the final verified-release decision is bound.
  Release-command orchestration is present; caller assembly is diagnostic-only
  and no accepting finalizer remains while the repository-owned signer policy
  is absent. Even a cryptographically valid caller-supplied signer/policy pair
  returns `FV2-E-WAVE6-SIGNER-AUTHORITY`. Signed
  evidence contains the canonical eight-gate manifest hash, and
  CLI admission rejects any gate/order/receipt mutation that does not match it.
  Gate 0 now has a typed collector over exact proof receipts, closed transitive
  axiom audits, and accepted fresh/independent replay closures for the same
  artifact. Gate 1 also has an additive Wave 6 V2 route over exhaustive
  instruction and terminator coverage, but rejects Exact promotion until a
  canonical typed transition manifest exists. Gate 2 binds executed woven→VIR
  construction to an ordered,
  independently validated compiler-certificate chain ending at the exact
  artifact. Gate 3 validates exact macro/AOP manifests, woven VIR provenance,
  advice proof material, and a sealed dynamic-transform lock, then fails closed
  because the compiler-owned manifest producer is missing; the remaining
  four product/release collectors are pending.
- REQ-FV2-014: the first SimpleOS typed source-promotion slice exhaustively compares
  the real capability-rights gate with an independent 9-bit subset
  specification over all 262,144 input pairs, requires a closed transitive Lean
  theorem audit, detects a zero-request mutant, binds semantic/trust/cache
  identities and invalidates stale keys. Raw axiom text produces only
  `model_proven`; `source_refined` additionally requires an exact
  `ProofReceiptV1`, independent replay closure, and source/model behavior-hash
  dependencies. The Lean `rights_allow9_sound` theorem now exists and checks
  with only `propext` and `Quot.sound`.
  A second explicitly bounded scheduler slice executes the real green-task
  completion transition for runnable, parked, done, and unknown state classes
  at minimum/zero/maximum result boundaries. It proves first-write-wins and
  stale park-reason clearing, kills both corresponding mutants, and binds one
  composite Lean root with only `propext`. Raw audit evidence remains
  `model_proven`; typed source promotion now additionally requires the exact
  composite proof receipt, source/model semantic dependencies, matching trust,
  and independent replay closure. The Lean model was corrected to clear
  `park_reason`, matching the product transition.
  A third exact IPC bridge covers `green_channel_close_drain`, including the
  product field omitted by the older broad model (`backpressure_count`). It
  preserves capacity and buffered FIFO contents, returns waiters in order,
  empties the waiter set, closes idempotently, and kills lost-buffer and
  lost-wakeup mutants. One composite Lean root uses only `propext`. Raw audit
  evidence remains `model_proven`; source promotion requires the exact typed
  root, source/model semantic dependencies, matching trust, and independent
  replay closure.
  The DBFS slice executes the real mutable `DbfsTxn.commit` boundary before and
  after WAL durability for active, committed, and aborted inputs. Its composite
  Lean root covers durability, success visibility, failure invisibility, and
  crash atomicity using only `propext`; typed promotion requires exact semantic
  dependencies, trust identity, and replay. Failed
  unflushed commits preserve status and remain crash-invisible; successful
  flushed commits become recoverably visible. An early-commit mutant is killed.
  Four universal Lean roots use only `propext`; raw evidence remains
  `model_proven`. This replaces no broader NVFS
  claim: multi-record replay and every persistence point remain open.
  The memory slice executes the real one-page `vmm_shared_unmap` boundary for
  a surviving shared reference, a dirty last reference, repeated unmap, and a
  private mapping. It requires survivor residency, last-reference writeback
  and retirement, private-reference framing, and idempotence; four transition
  mutants must be killed. Four exact Lean roots use only `propext`, and the
  receipt remains explicitly bounded at `model_proven` and below artifact verification.
  A composite Lean root covers all four unmap guarantees using only `propext`;
  typed source promotion requires that exact root, source/model semantic
  dependencies, matching trust identity, and replay closure.
  The process slice executes the real Scheduler create/clone, live wait,
  child-exit, wake, status collection, slot removal, and second-collection
  rejection chain. Its exact Lean bridge proves the same four transitions with
  one `propext`-only root. Typed promotion requires exact source/model hashes
  and replay; orphan adoption remains outside this bounded slice.
  The process-queue slice executes two FIFO sends with an attached handle,
  rejects a third at capacity, receives both payloads and handle identities in
  order, closes the send side, observes EOF after drain and `EPIPE` on send,
  then destroys/recreates the slot and rejects the stale generation. Its
  composite Lean root uses `propext` and `Quot.sound`; typed promotion remains
  replay-bound and below artifact verification.
- REQ-FV2-015: a bounded RV32 ADD slice now composes its typed instruction
  provider, trap-priority projection, and sequential retirement owner into real
  strict-HWIR VHDL. Its RVFI wrapper derives architectural outputs from the
  same retirement owner and captures source operands on `dispatch_accept` so
  stalls cannot relabel live inputs as an older retirement. Loads fail closed
  at the disabled LSU seam. Lean 4.33 checks
  exact wrapping ADD, x0 suppression, PC advance, reachability, and a detected
  subtraction mutant. This remains below product verification until generated
  Sail differential and final artifact evidence land.
  Generated proof, reachability-cover, and subtraction-mutant SBY jobs have
  distinct hashes. Caller-constructed job objects exercise only the protocol
  and reduce to `specified`. Executed external evidence must bind module,
  HWIR, RTL, RVFI contract, assumptions, every generated input, outputs, and
  engine identities before reaching `model_proven`. Timeout, unknown,
  swapped-job, cross-module receipt, or surviving mutant results reduce to
  `failed`. A separate GHDL/Yosys lane proves the exact `synth -top`
  transformation equivalent, retains the synthesized JSON netlist, and binds
  module, RTL, netlist, proof log, tool identities, and synthesis-policy hash.
  Only the combined exact receipt reaches `backend_refined`, which still cannot
  authorize release. The end-to-end generator/runner exists but currently
  exits 2 on the Rust seed. Pinned Sail Zca classification evidence passes and
  explicitly makes no ADD equivalence claim. The separate ADD Sail wrapper
  compiles exact opcode `002081b3`, requires a pinned RV32 configuration and
  the architectural result x3=12, and binds the model, configuration, ELF,
  disassembly, trace, HWIR, and RTL identities. It currently exits 2 because
  the pinned simulator/config are absent; its parser and negative cases remain
  host-independent evidence only.

## Scenarios

### Simple Formal Verification 2.0 foundation gates

### REQ-FV2-001 and NFR-FV2-002: truthful fail-closed formal status

#### should classify Lean-only success as model-proven
#### should reserve release permission for artifact verification

- should reserve release permission for artifact verification
- Compare model and artifact release states
   - Expected: FormalStatus.SourceRefined.permits_verified_release() is false
   - Expected: FormalStatus.BackendRefined.permits_verified_release() is false
   - Expected: FormalStatus.ArtifactVerified.permits_verified_release() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should reserve release permission for artifact verification")
step("Compare model and artifact release states")
expect(FormalStatus.SourceRefined.permits_verified_release()).to_equal(false)
expect(FormalStatus.BackendRefined.permits_verified_release()).to_equal(false)
expect(FormalStatus.ArtifactVerified.permits_verified_release()).to_equal(true)
```

</details>

#### should reject a claimed artifact receipt with missing refinement evidence

- should reject a claimed artifact receipt with missing refinement evidence
- Validate an incomplete artifact receipt
   - Expected: receipt.permits_verified_release() is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should reject a claimed artifact receipt with missing refinement evidence")
step("Validate an incomplete artifact receipt")
val receipt = ProofReceiptV1("root", FormalStatus.ArtifactVerified, "key", "artifact", [], "axioms", "trust", "", "")
expect(receipt.permits_verified_release()).to_equal(false)
expect(receipt.diagnostic()).to_contain("COMPILER")
```

</details>

### REQ-FV2-019 and NFR-FV2-003: fail-closed verified release decision

#### should accept only complete artifact-bound executed evidence

- should accept only complete artifact-bound executed evidence
- Evaluate exact artifact proof compiler trust replay mutation and cover identities
   - Expected: evaluate_verified_release_v1(evidence).passed() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should accept only complete artifact-bound executed evidence")
step("Evaluate exact artifact proof compiler trust replay mutation and cover identities")
val evidence = VerifiedReleaseEvidenceV1("verified",
    FormalStatus.ArtifactVerified, [FormalStatus.ArtifactVerified],
    sha256_text("artifact"), sha256_text("artifact"),
    [sha256_text("proof")], [sha256_text("compiler")],
    sha256_text("trust"), "", sha256_text("replay"),
    sha256_text("mutation"), sha256_text("non-vacuity"),
    [ReleaseEvidenceOutcomeV1.ProvedWithCertificate], 0, 0, 0, 0,
    sha256_text("delivery-gates"))
expect(evaluate_verified_release_v1(evidence).passed()).to_equal(true)
```

</details>

#### should reject unknown timeout missing-tool stale unsupported and environment failures

- should reject unknown timeout missing-tool stale unsupported and environment failures
- Reject stale or unsupported evidence
   - Expected: evaluate_verified_release_v1(evidence).passed() is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 17 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should reject unknown timeout missing-tool stale unsupported and environment failures")
step("Reject stale or unsupported evidence")
val outcomes = [ReleaseEvidenceOutcomeV1.Unknown,
    ReleaseEvidenceOutcomeV1.Timeout,
    ReleaseEvidenceOutcomeV1.MissingTool,
    ReleaseEvidenceOutcomeV1.ToolFailure,
    ReleaseEvidenceOutcomeV1.EnvironmentFailure]
for outcome in outcomes:
    val evidence = VerifiedReleaseEvidenceV1("verified",
        FormalStatus.ArtifactVerified, [FormalStatus.ArtifactVerified],
        sha256_text("artifact"), sha256_text("artifact"),
        [sha256_text("proof")], [sha256_text("compiler")],
        sha256_text("trust"), "", sha256_text("replay"),
        sha256_text("mutation"), sha256_text("non-vacuity"),
        [outcome], 1, 1, 0, 1, sha256_text("delivery-gates"))
    expect(evaluate_verified_release_v1(evidence).passed()).to_equal(false)
```

</details>

#### should pin signer policy outside the caller-controlled CLI boundary

- should pin signer policy outside the caller-controlled CLI boundary
- Accept one bundle path and reject policy or status injection
   - Expected: verify_option_error(["release", "bundle.sdn"]) equals ``
   - Expected: verify_option_error(["release", "--verified"]) == "" is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should pin signer policy outside the caller-controlled CLI boundary")
step("Accept one bundle path and reject policy or status injection")
expect(verify_option_error(["release", "bundle.sdn"])).to_equal("")
expect(verify_option_error(["release", "bundle.sdn",
    "attacker-policy.sdn"]) == "").to_equal(false)
expect(verify_option_error(["release", "--verified"]) == "").to_equal(false)
```

</details>

### REQ-FV2-020 and NFR-FV2-010: ordered formal delivery gates

#### should preserve an honest partial plan without implying release readiness

- should preserve an honest partial plan without implying release readiness
- Pass truth semantics VIR and AOP then retain every product gate as blocked
   - Expected: decision.accepted_state is true
   - Expected: decision.release_ready is false
   - Expected: decision.highest_passed_gate equals `aop_macro_closure`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should preserve an honest partial plan without implying release readiness")
step("Pass truth semantics VIR and AOP then retain every product gate as blocked")
val decision = check_fv2_gate(setup_fv2_fixture(4), nil)
expect(decision.accepted_state).to_equal(true)
expect(decision.release_ready).to_equal(false)
expect(decision.highest_passed_gate).to_equal("aop_macro_closure")
```

</details>

#### should reject a product gate that jumps over an unmet predecessor

- should reject a product gate that jumps over an unmet predecessor
- Attempt SimpleOS promotion while VIR and AOP gates remain blocked
   - Expected: decision.accepted_state is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should reject a product gate that jumps over an unmet predecessor")
step("Attempt SimpleOS promotion while VIR and AOP gates remain blocked")
var evidence = fv2_delivery_plan(2)
evidence[4] = fv2_delivery_evidence(
    FormalDeliveryGateV1.SimpleOsVerticalSlice, true)
val decision = evaluate_formal_delivery_gates_v1(evidence, nil)
expect(decision.accepted_state).to_equal(false)
expect(decision.diagnostic).to_contain("PREMATURE")
```

</details>

#### should require the exact final release decision after all eight gates

- should require the exact final release decision after all eight gates
- Close the ordered gate chain and bind its verified release decision
   - Expected: decision.release_ready is true
   - Expected: decision.highest_passed_gate equals `verified_release`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should require the exact final release decision after all eight gates")
step("Close the ordered gate chain and bind its verified release decision")
val decision = evaluate_formal_delivery_gates_v1(
    fv2_delivery_plan(8), Some(fv2_passed_release_bundle()))
expect(decision.release_ready).to_equal(true)
expect(decision.highest_passed_gate).to_equal("verified_release")
```

</details>

### REQ-FV2-004 and NFR-FV2-007: execution-linked contracts

#### should retain source predicates outside the executable body

- should retain source predicates outside the executable body
- Parse a function with entry and actual-result contracts
   - Expected: fn_.contract.preconditions.len() equals `1`
   - Expected: fn_.contract.postconditions.len() equals `1`
   - Expected: fn_.body.stmts.len() equals `1`
   - Expected: fn_.contract.preconditions[0].span.file equals `fv2_system_contract.spl`


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should retain source predicates outside the executable body")
step("Parse a function with entry and actual-result contracts")
val module = parse_and_build_module(
    "fn increment(x: i64) -> i64:\n" +
    "    in:\n        x >= 0\n" +
    "    out(ret):\n        ret > x\n" +
    "    x + 1\n", "fv2_system_contract.spl")
val fn_ = module.functions["increment"]
expect(fn_.contract.preconditions.len()).to_equal(1)
expect(fn_.contract.postconditions.len()).to_equal(1)
expect(fn_.body.stmts.len()).to_equal(1)
expect(fn_.contract.preconditions[0].span.file).to_equal("fv2_system_contract.spl")
```

</details>

#### should generate non-vacuity and actual-call theorem roots

- should generate non-vacuity and actual-call theorem roots
- Render a contract over the emitted function execution
   - Expected: lean does not contain `∃ result`


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should generate non-vacuity and actual-call theorem roots")
step("Render a contract over the emitted function execution")
var builder = LeanBuilder.create()
val contract = FunctionContract("increment", ["x = x"],
    ["result = x + 1"], [], [], [], "", "Increment.correct")
contract.to_lean_spec(builder, [("x", "BitVec 64")], "BitVec 64")
val lean = builder.build()
expect(lean).to_contain("increment_preconditions_satisfiable")
expect(lean).to_contain("let result : BitVec 64 := increment x")
expect(lean).to_contain("Increment.correct_preconditions_satisfiable")
expect(lean.contains("∃ result")).to_equal(false)
```

</details>

#### should bind the exact proof root and source map into contract identity

- should bind the exact proof root and source map into contract identity
- Compare two otherwise-identical retained contract snapshots
   - Expected: first.hash() == second.hash() is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should bind the exact proof root and source map into contract identity")
step("Compare two otherwise-identical retained contract snapshots")
val clause = VerificationContractClauseV1("requires",
    VerificationContractClauseKindV1.Requires, "predicate", "bool",
    "file=fv2.spl|start=1|end=2|line=1|col=1", "", [])
val first = VerificationFunctionContractV1(
    "VerificationFunctionContract-v1", "42", "woven",
    VerificationContractOutcomeV1.Plain, [clause], "Proof.first")
val second = VerificationFunctionContractV1(
    "VerificationFunctionContract-v1", "42", "woven",
    VerificationContractOutcomeV1.Plain, [clause], "Proof.second")
expect(first.hash() == second.hash()).to_equal(false)
val unmapped = VerificationContractClauseV1("requires",
    VerificationContractClauseKindV1.Requires, "predicate", "bool", "", "", [])
expect(unmapped.diagnostic()).to_contain("SPAN")
```

</details>

#### should require exact state authorities for invariant frame and termination VCs

- should require exact state authorities for invariant frame and termination VCs
- Attempt invariant generation without reachable-state semantics
- Bind initialization and preservation to independent semantic identities
   - Expected: complete.diagnostic equals ``
   - Expected: complete.obligations[0].kind equals `ExecutionContractObligationKindV1.InvariantInitialization`
   - Expected: complete.obligations[1].kind equals `ExecutionContractObligationKindV1.InvariantPreservation`
   - Expected: complete.obligations[0].relation_semantic_hash == complete.obligations[1].relation_semantic_hash is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 21 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should require exact state authorities for invariant frame and termination VCs")
step("Attempt invariant generation without reachable-state semantics")
val invariant = VerificationContractClauseV1("invariant",
    VerificationContractClauseKindV1.StatePredicate, "predicate", "bool",
    "file=fv2.spl|start=3|end=4|line=2|col=1", "", [])
val contract = VerificationFunctionContractV1(
    "VerificationFunctionContract-v1", "43", "woven",
    VerificationContractOutcomeV1.Plain, [invariant], "")
val incomplete = generate_execution_contract_obligations_with_context_v2(
    contract, ExecutionContractSemanticContextV2("exec", "", "", "transition", "", "", ""))
expect(incomplete.diagnostic).to_contain("INVARIANT-REACHABLE")

step("Bind initialization and preservation to independent semantic identities")
val complete = generate_execution_contract_obligations_with_context_v2(
    contract, ExecutionContractSemanticContextV2(
        "exec", "", "reachable", "transition", "", "", ""))
expect(complete.diagnostic).to_equal("")
expect(complete.obligations[0].kind).to_equal(ExecutionContractObligationKindV1.InvariantInitialization)
expect(complete.obligations[1].kind).to_equal(ExecutionContractObligationKindV1.InvariantPreservation)
expect(complete.obligations[0].relation_semantic_hash == complete.obligations[1].relation_semantic_hash).to_equal(false)
```

</details>

### REQ-FV2-002: verified assurance profile

#### should expose verified as the strictest canonical rung

- should expose verified as the strictest canonical rung
- Read the canonical assurance ladder
   - Expected: canonical_profile_names() equals `["moderate", "strict", "robust", "critical", "verified"]`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should expose verified as the strictest canonical rung")
step("Read the canonical assurance ladder")
expect(canonical_profile_names()).to_equal(["moderate", "strict", "robust", "critical", "verified"])
expect(AssuranceStrictnessV2.Verified.rank()).to_be_greater_than(AssuranceStrictnessV2.Critical.rank())
```

</details>

#### should inherit critical engineering restrictions

- should inherit critical engineering restrictions
- Compare strictness through the typed resolver
   - Expected: policy.strictness.at_least(AssuranceStrictnessV2.Critical) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should inherit critical engineering restrictions")
step("Compare strictness through the typed resolver")
val policy = policy_for_profile_name_v2("verified")
expect(policy.strictness.at_least(AssuranceStrictnessV2.Critical)).to_equal(true)
```

</details>

#### should never let a lower CLI input weaken a verified project pin

- should never let a lower CLI input weaken a verified project pin
- Resolve project and CLI inputs with raise-only precedence
   - Expected: policy.strictness equals `AssuranceStrictnessV2.Verified`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should never let a lower CLI input weaken a verified project pin")
step("Resolve project and CLI inputs with raise-only precedence")
val policy = resolve_assurance_policy_v2("verified", "moderate", "", "nogc_async_mut_noalloc", "none", "none")
expect(policy.strictness).to_equal(AssuranceStrictnessV2.Verified)
```

</details>

### REQ-FV2-006 and NFR-FV2-008: exact and fail-closed semantics

#### should preserve machine width and signed interpretation

- should preserve machine width and signed interpretation
- Lower signed and unsigned machine integers
   - Expected: verification_ir_type(MirType(kind: MirTypeKind.I32)).representation equals `bitvec:32:signed`
   - Expected: verification_ir_type(MirType(kind: MirTypeKind.U32)).representation equals `bitvec:32:unsigned`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should preserve machine width and signed interpretation")
step("Lower signed and unsigned machine integers")
expect(verification_ir_type(MirType(kind: MirTypeKind.I32)).representation).to_equal("bitvec:32:signed")
expect(verification_ir_type(MirType(kind: MirTypeKind.U32)).representation).to_equal("bitvec:32:unsigned")
```

</details>

#### should reject floating-point semantics until IEEE behavior is exact

- should reject floating-point semantics until IEEE behavior is exact
- Classify an unsupported floating-point type
   - Expected: verification_ir_type(MirType(kind: MirTypeKind.F64)).semantic_class equals `SemanticClass.Unsupported`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should reject floating-point semantics until IEEE behavior is exact")
step("Classify an unsupported floating-point type")
expect(verification_ir_type(MirType(kind: MirTypeKind.F64)).semantic_class).to_equal(SemanticClass.Unsupported)
```

</details>

#### should reject pointers without region and capability semantics

- should reject pointers without region and capability semantics
- Classify a raw mutable pointer
   - Expected: pointer.closure_ready() is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should reject pointers without region and capability semantics")
step("Classify a raw mutable pointer")
val pointer = verification_ir_type(MirType(kind: MirTypeKind.Ptr(MirType.i64(), true)))
expect(pointer.closure_ready()).to_equal(false)
expect(pointer.diagnostic).to_contain("POINTER")
```

</details>

#### should make the canonical MIR backend emit exact-width BitVec types

- should make the canonical MIR backend emit exact-width BitVec types
- Inspect signed and unsigned canonical Lean backend types
   - Expected: mir_type_to_lean(MirType(kind: MirTypeKind.I32)).ok().unwrap() equals `BitVec 32`
   - Expected: mir_type_to_lean(MirType(kind: MirTypeKind.U64)).ok().unwrap() equals `BitVec 64`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should make the canonical MIR backend emit exact-width BitVec types")
step("Inspect signed and unsigned canonical Lean backend types")
expect(mir_type_to_lean(MirType(kind: MirTypeKind.I32)).ok().unwrap()).to_equal("BitVec 32")
expect(mir_type_to_lean(MirType(kind: MirTypeKind.U64)).ok().unwrap()).to_equal("BitVec 64")
```

</details>

#### should retain exact Result payload types through MIR, VIR, and Lean

- should retain exact Result payload types through MIR, VIR, and Lean
- Classify and print a machine-typed normal/error outcome
   - Expected: verification_ir_type(result_type).representation equals `result<bitvec:32:signed,bitvec:8:unsigned>`
   - Expected: mir_type_to_lean(result_type).ok().unwrap() equals `Except (BitVec 8) (BitVec 32)`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should retain exact Result payload types through MIR, VIR, and Lean")
step("Classify and print a machine-typed normal/error outcome")
val result_type = MirType.result(MirType(kind: MirTypeKind.I32), MirType(kind: MirTypeKind.U8))
expect(verification_ir_type(result_type).representation).to_equal("result<bitvec:32:signed,bitvec:8:unsigned>")
expect(mir_type_to_lean(result_type).ok().unwrap()).to_equal("Except (BitVec 8) (BitVec 32)")
```

</details>

#### should reject canonical backend operations needing missing exact semantics

- should reject canonical backend operations needing missing exact semantics
- Attempt lossy float and signedness-ambiguous arithmetic lowering
   - Expected: mir_type_to_lean(MirType(kind: MirTypeKind.F64)).is_err() is true
   - Expected: translate_binop(MirBinOp.Div).is_err() is true
   - Expected: translate_binop(MirBinOp.Shr).is_err() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should reject canonical backend operations needing missing exact semantics")
step("Attempt lossy float and signedness-ambiguous arithmetic lowering")
expect(mir_type_to_lean(MirType(kind: MirTypeKind.F64)).is_err()).to_equal(true)
expect(translate_binop(MirBinOp.Div).is_err()).to_equal(true)
expect(translate_binop(MirBinOp.Shr).is_err()).to_equal(true)
```

</details>

### REQ-FV2-007: typed Lean generation

#### should print a typed execution-linked term deterministically

- should print a typed execution-linked term deterministically
- Construct and render a typed Lean contract term


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should print a typed execution-linked term deterministically")
step("Construct and render a typed Lean contract term")
val x = LeanBinderIR("x", LeanTypeIR.BitVec(32))
val call = LeanTermIR.Apply("increment", [LeanTermIR.Var("x")])
val post = LeanTermIR.Binary(LeanBinaryOpIR.Equal, LeanTermIR.Var("result"), LeanTermIR.Var("x"))
val term = LeanTermIR.Forall([x], LeanTermIR.Let(LeanBinderIR("result", LeanTypeIR.BitVec(32)), call, post))
expect(fv2_render(term)).to_contain("let result : BitVec 32 := increment x")
```

</details>

#### should reject invalid typed nodes before printing

- should reject invalid typed nodes before printing
- Validate an impossible bit-vector width
   - Expected: fv2_render(invalid) equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should reject invalid typed nodes before printing")
step("Validate an impossible bit-vector width")
val invalid = LeanTermIR.BitVecLiteral(0, 0)
expect(invalid.diagnostic()).to_contain("WIDTH")
expect(fv2_render(invalid)).to_equal("")
```

</details>

#### should require explicit proof ownership

- should require explicit proof ownership
- Validate a theorem without a proof reference


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should require explicit proof ownership")
step("Validate a theorem without a proof reference")
val theorem = LeanTheoremIR("unsafe_claim", LeanTermIR.TrueProp, "")
expect(theorem.diagnostic()).to_contain("PROOF")
```

</details>

### REQ-FV2-003 REQ-FV2-005 REQ-FV2-008 and NFR-FV2-001 NFR-FV2-005: canonical verification evidence

#### should require a resolver-bound direct-call manifest for V2 module VIR

- should require a resolver-bound direct-call manifest for V2 module VIR
- Construct canonical verification evidence
   - Expected: validate_resolved_direct_call_manifest_v1(module, manifest).closed() is true
- Construct V2 VIR from the same resolver-bound snapshot
   - Expected: vir.closure_ready() is true
   - Expected: vir.resolved_call_manifest_hash equals `manifest.hash()`
- Invalidate the V2 semantic identity when resolver evidence drifts
   - Expected: drifted.closure_ready() is true
   - Expected: vir.semantic_hash == drifted.semantic_hash is false
- Reject a missing call binding before effects or calls can close
   - Expected: rejected.closure_ready() is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 33 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should require a resolver-bound direct-call manifest for V2 module VIR")
step("Construct canonical verification evidence")
val module = fv2_resolved_global_writer_module()
val manifest = fv2_resolved_global_writer_manifest(module)
expect(validate_resolved_direct_call_manifest_v1(module, manifest).closed()).to_equal(true)

step("Construct V2 VIR from the same resolver-bound snapshot")
val vir = verification_ir_module_from_resolved_mir_v2(module,
    sha256_text("source"), sha256_text("expanded"),
    sha256_text("woven"), sha256_text("policy"), manifest)
expect(vir.closure_ready()).to_equal(true)
expect(vir.resolved_call_manifest_hash).to_equal(manifest.hash())

step("Invalidate the V2 semantic identity when resolver evidence drifts")
var drifted_manifest = manifest
drifted_manifest.resolver_receipt_hash = sha256_text(
    "fv2-system-resolver-receipt-drift")
val drifted = verification_ir_module_from_resolved_mir_v2(module,
    sha256_text("source"), sha256_text("expanded"),
    sha256_text("woven"), sha256_text("policy"), drifted_manifest)
expect(drifted.closure_ready()).to_equal(true)
expect(vir.semantic_hash == drifted.semantic_hash).to_equal(false)

step("Reject a missing call binding before effects or calls can close")
val absent = ResolvedDirectCallManifestV1(
    resolved_direct_call_module_hash_v1(module),
    sha256_text("fv2-system-resolver-receipt"), [])
val rejected = verification_ir_module_from_resolved_mir_v2(module,
    sha256_text("source"), sha256_text("expanded"),
    sha256_text("woven"), sha256_text("policy"), absent)
expect(rejected.closure_ready()).to_equal(false)
expect(rejected.diagnostic).to_contain("CALL-IDENTITY-MISSING")
```

</details>

#### should derive VC authorities from canonical MIR and retained contracts

- should derive VC authorities from canonical MIR and retained contracts
- Derive type contract effect frame backend and trust identities without caller labels
   - Expected: closure.closed() is true
   - Expected: closure.obligations.len() equals `13`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should derive VC authorities from canonical MIR and retained contracts")
step("Derive type contract effect frame backend and trust identities without caller labels")
val trust = TrustManifestV1(["propext"], [], [], [], [], [])
val closure = generate_verification_obligation_closure_from_canonical_mir_v1(
    fv2_canonical_vc_function(), "woven-global-writer", "lean4",
    "lean-backend-v1", trust)
expect(closure.closed()).to_equal(true)
expect(closure.obligations.len()).to_equal(13)
expect(closure.root_obligation_id).to_equal(
    "8801::fv2::trust-closure")
```

</details>

#### should generate one deterministic fail-closed thirteen-kind DAG

- should generate one deterministic fail-closed thirteen-kind DAG
- Bind every required VC class into the final trust-closure root
   - Expected: closure.closed() is true
   - Expected: closure.obligations.len() equals `13`


<details>
<summary>Executable SSpec</summary>

Runnable source: 18 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should generate one deterministic fail-closed thirteen-kind DAG")
step("Bind every required VC class into the final trust-closure root")
val authorities = VerificationClosureAuthoritiesV1(
    "sample::verified", "sample.spl:10",
    assurance_text_hash("type"), assurance_text_hash("pre"),
    assurance_text_hash("termination"), assurance_text_hash("memory"),
    assurance_text_hash("effect"), assurance_text_hash("normal"),
    assurance_text_hash("error"), assurance_text_hash("invariant-init"),
    assurance_text_hash("invariant-preserve"), assurance_text_hash("calls"),
    assurance_text_hash("witness"), assurance_text_hash("lowering"),
    assurance_text_hash("trust"))
val closure = generate_verification_obligation_closure_v1(authorities)
expect(closure.closed()).to_equal(true)
expect(closure.obligations.len()).to_equal(13)
expect(closure.root_obligation_id).to_end_with("::fv2::trust-closure")
expect(closure.obligations[12].dependency_ids).to_contain(
    "sample::verified::fv2::backend-lowering-coverage")
```

</details>

#### should reject an absent typed proposition identity

- should reject an absent typed proposition identity
- Remove one VC authority and require a closed diagnostic
   - Expected: closure.closed() is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should reject an absent typed proposition identity")
step("Remove one VC authority and require a closed diagnostic")
val authorities = VerificationClosureAuthoritiesV1(
    "sample::verified", "sample.spl:10",
    assurance_text_hash("type"), assurance_text_hash("pre"),
    assurance_text_hash("termination"), assurance_text_hash("memory"),
    assurance_text_hash("effect"), "", assurance_text_hash("error"),
    assurance_text_hash("invariant-init"),
    assurance_text_hash("invariant-preserve"), assurance_text_hash("calls"),
    assurance_text_hash("witness"), assurance_text_hash("lowering"),
    assurance_text_hash("trust"))
val closure = generate_verification_obligation_closure_v1(authorities)
expect(closure.closed()).to_equal(false)
expect(closure.diagnostic).to_contain("AUTHORITY")
```

</details>

### REQ-FV2-009 and NFR-FV2-009: transitive trust and independent replay

#### should accept a complete report containing only Lean logic axioms

- should accept a complete report containing only Lean logic axioms
- Replay the shipped artifact independently
   - Expected: replay.accepted is true
   - Expected: audit.status equals `TrustAuditStatus.Closed`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should accept a complete report containing only Lean logic axioms")
step("Replay the shipped artifact independently")
val replay = check_fv2_replay(
    fv2_capability_replay_checker(ReplayCheckerClassV1.FreshLeanKernel),
    fv2_capability_replay_checker(ReplayCheckerClassV1.IndependentKernel))
expect(replay.accepted).to_equal(true)
val audit = audit_lean_axiom_report("declaration Safe.root depends on axioms: [propext, Quot.sound, Classical.choice]", ["Safe.root"], [])
expect(audit.status).to_equal(TrustAuditStatus.Closed)
```

</details>

#### should reject hidden project axioms and trusted native evaluation

- should reject hidden project axioms and trusted native evaluation
- Audit forbidden transitive dependencies
   - Expected: audit.status equals `TrustAuditStatus.Rejected`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should reject hidden project axioms and trusted native evaluation")
step("Audit forbidden transitive dependencies")
val audit = audit_lean_axiom_report("declaration Safe.root depends on axioms: [Board.hidden, Lean.trustCompiler]", ["Safe.root"], [])
expect(audit.status).to_equal(TrustAuditStatus.Rejected)
expect(audit.rejected_axioms).to_contain("Lean.trustCompiler")
```

</details>

#### should fail closed when a requested root has no report

- should fail closed when a requested root has no report
- Request two roots from a one-root report
   - Expected: audit.status equals `TrustAuditStatus.Missing`
   - Expected: audit.audited_root_count equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should fail closed when a requested root has no report")
step("Request two roots from a one-root report")
val audit = audit_lean_axiom_report("declaration Safe.first depends on axioms: []", ["Safe.first", "Safe.second"], [])
expect(audit.status).to_equal(TrustAuditStatus.Missing)
expect(audit.audited_root_count).to_equal(1)
```

</details>

#### should reject a proof-root prefix collision

- should reject a proof-root prefix collision
- Audit exact theorem identity
   - Expected: audit.status equals `TrustAuditStatus.Missing`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should reject a proof-root prefix collision")
step("Audit exact theorem identity")
val audit = audit_lean_axiom_report("declaration Safe.rootForged depends on axioms: []", ["Safe.root"], [])
expect(audit.status).to_equal(TrustAuditStatus.Missing)
```

</details>

### REQ-FV2-010 and NFR-FV2-004 NFR-FV2-006: evidence cache and scheduling identity

#### should invalidate evidence when the weave identity changes

- should invalidate evidence when the weave identity changes
- Compare two semantic cache identities
   - Expected: fv2_key("weave-a").hash() == fv2_key("weave-b").hash() is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should invalidate evidence when the weave identity changes")
step("Compare two semantic cache identities")
expect(fv2_key("weave-a").hash() == fv2_key("weave-b").hash()).to_equal(false)
```

</details>

#### should reject reuse under a stale cache key

- should reject reuse under a stale cache key
- Bind an artifact receipt to the old semantic key
   - Expected: receipt.reusable_for(fv2_key("weave-b")) is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should reject reuse under a stale cache key")
step("Bind an artifact receipt to the old semantic key")
val old_key = fv2_key("weave-a")
val receipt = ProofReceiptV1("Safe.root", FormalStatus.ArtifactVerified, old_key.hash(), "artifact", [], "axioms", "trust", "compiler", "replay")
expect(receipt.reusable_for(fv2_key("weave-b"))).to_equal(false)
```

</details>

#### should require a closed matching trust manifest for an unqualified release

- should require a closed matching trust manifest for an unqualified release
- Evaluate closed-release policy with an environmental assumption


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should require a closed matching trust manifest for an unqualified release")
step("Evaluate closed-release policy with an environmental assumption")
val trust = TrustManifestV1(["propext"], [], [], [], [], ["timer monotonic"])
val key = fv2_key("weave")
val certificate = fv2_compiler_certificate()
val receipt = ProofReceiptV1("Safe.root", FormalStatus.ArtifactVerified, key.hash(), "artifact", [], "axioms", sha256_text(trust.canonical_text()), certificate.expected_certificate_hash(), "replay")
val replay = IndependentReplayClosureV1(
    "IndependentReplayClosure-v1", "", "", "", false,
    "environmental trust is not replay closure")
expect(permits_closed_verified_release(
    policy_for_profile_name_v2("verified"), key, receipt, trust,
    certificate, replay)).to_equal(false)
```

</details>

#### should schedule a recursive proof component after its dependencies

- should schedule a recursive proof component after its dependencies
- Build the SymbolId SCC proof schedule
   - Expected: schedule.diagnostic equals ``
   - Expected: schedule.ordered_components.len() equals `3`
   - Expected: schedule.ordered_components[0].symbol_ids[0] equals `type`


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should schedule a recursive proof component after its dependencies")
step("Build the SymbolId SCC proof schedule")
val schedule = build_proof_dag_schedule_v1([
    ProofDagNodeV1("api", ["even"], "api", 2),
    ProofDagNodeV1("even", ["odd", "type"], "even", 3),
    ProofDagNodeV1("odd", ["even"], "odd", 3),
    ProofDagNodeV1("type", [], "type", 1)
])
expect(schedule.diagnostic).to_equal("")
expect(schedule.ordered_components.len()).to_equal(3)
expect(schedule.ordered_components[0].symbol_ids[0]).to_equal("type")
```

</details>

#### should invalidate the reverse dependency closure but retain unrelated proofs

- should invalidate the reverse dependency closure but retain unrelated proofs
- Change one semantic SymbolId
   - Expected: affected.join(",") equals `api,logic,type`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should invalidate the reverse dependency closure but retain unrelated proofs")
step("Change one semantic SymbolId")
val affected = proof_dag_affected_symbols([
    ProofDagNodeV1("api", ["logic"], "api", 1),
    ProofDagNodeV1("logic", ["type"], "logic", 1),
    ProofDagNodeV1("type", [], "type", 1),
    ProofDagNodeV1("unrelated", [], "unrelated", 1)
], ["type"])
expect(affected.join(",")).to_equal("api,logic,type")
```

</details>

#### should reject a proof graph whose private helper is outside closure

- should reject a proof graph whose private helper is outside closure
- Resolve a missing dependency


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should reject a proof graph whose private helper is outside closure")
step("Resolve a missing dependency")
val schedule = build_proof_dag_schedule_v1([
    ProofDagNodeV1("api", ["unchecked-helper"], "api", 1)
])
expect(schedule.diagnostic).to_contain("DEPENDENCY")
```

</details>

### REQ-FV2-011 and NFR-FV2-005: canonical AOP and macro closure

#### should make advice order part of the weave hash

- should make advice order part of the weave hash
- Hash two opposite advice orders
   - Expected: first.hash() == second.hash() is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should make advice order part of the weave hash")
step("Hash two opposite advice orders")
val first = WeaveManifestV1("base", "macro", [WeaveJoinPointV1("42", ["before", "after"])], [], "woven")
val second = WeaveManifestV1("base", "macro", [WeaveJoinPointV1("42", ["after", "before"])], [], "woven")
expect(first.hash() == second.hash()).to_equal(false)
```

</details>

#### should reject unstable join-point ordering

- should reject unstable join-point ordering
- Validate a manifest with descending SymbolIds


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should reject unstable join-point ordering")
step("Validate a manifest with descending SymbolIds")
val manifest = WeaveManifestV1("base", "macro", [WeaveJoinPointV1("9", []), WeaveJoinPointV1("2", [])], [], "woven")
expect(manifest.diagnostic()).to_contain("ORDER")
```

</details>

#### should reject behavior refinement without exactly-once proceed

- should reject behavior refinement without exactly-once proceed
- Validate an incomplete around-advice certificate


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should reject behavior refinement without exactly-once proceed")
step("Validate an incomplete around-advice certificate")
val certificate = AspectCertificateV1("around", AspectEvidenceClassV1.BehaviorRefinement, "base", "woven", "proof", true, false)
expect(certificate.diagnostic()).to_contain("PROCEED")
```

</details>

### REQ-FV2-012: typed effects

#### should propagate a generated helper effect into its public caller

- should propagate a generated helper effect into its public caller
- Resolve transitive typed effects
   - Expected: closure.diagnostic equals ``
   - Expected: public_effects[0].canonical_text() equals `write:kernel.heap`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should propagate a generated helper effect into its public caller")
step("Resolve transitive typed effects")
val closure = resolve_verification_effect_closure([
    VerificationEffectNodeV1("public", [VerificationEffectV1.Pure], ["generated"], []),
    VerificationEffectNodeV1("generated", [VerificationEffectV1.Write("kernel.heap")], [], [])
])
expect(closure.diagnostic).to_equal("")
val public_effects = closure.effects_for("public").unwrap()
expect(public_effects[0].canonical_text()).to_equal("write:kernel.heap")
```

</details>

#### should reject an unbound MMIO region

- should reject an unbound MMIO region
- Validate an incomplete MMIO effect


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should reject an unbound MMIO region")
step("Validate an incomplete MMIO effect")
expect(VerificationEffectV1.MMIO("").diagnostic()).to_contain("REGION")
```

</details>

#### should reject an unresolved indirect call target

- should reject an unresolved indirect call target
- Resolve an incomplete call graph


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should reject an unresolved indirect call target")
step("Resolve an incomplete call graph")
val closure = resolve_verification_effect_closure([
    VerificationEffectNodeV1("public", [VerificationEffectV1.Pure], [], ["call@source:42"])
])
expect(closure.diagnostic).to_contain("INDIRECT")
```

</details>

#### should derive global effects from MIR and reject a forged pure claim

- should derive global effects from MIR and reject a forged pure claim
- Derive an exact global write manifest
   - Expected: manifest.closed() is true
   - Expected: manifest.effects[0].region_id equals `global:77`
- Attempt to replace the derived write with caller-supplied pure
   - Expected: vir.closure_ready() is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should derive global effects from MIR and reject a forged pure claim")
step("Derive an exact global write manifest")
val func = fv2_global_writer()
val manifest = verification_region_effect_manifest_v1(func)
expect(manifest.closed()).to_equal(true)
expect(manifest.effects[0].region_id).to_equal("global:77")
expect(manifest.effects[0].source_span).to_contain("fv2_global_writer.spl")

step("Attempt to replace the derived write with caller-supplied pure")
val vir = verification_ir_from_retained_contract(
    func, "source", "expanded", "woven", "policy",
    [VerificationEffectV1.Pure], [])
expect(vir.closure_ready()).to_equal(false)
expect(vir.diagnostic).to_contain("EFFECT-MISMATCH")
```

</details>

#### should bind transitive direct-call effects into canonical module VIR

- should bind transitive direct-call effects into canonical module VIR
- Build module VIR from exact internal SymbolIds
   - Expected: vir.closure_ready() is true
   - Expected: vir.functions[1].called_symbols equals `[`
   - Expected: vir.functions[1].effects equals `[`
   - Expected: vir.effect_closure_hash == "" is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 18 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should bind transitive direct-call effects into canonical module VIR")
step("Build module VIR from exact internal SymbolIds")
val writer = fv2_global_writer()
val caller = fv2_global_writer_caller()
var functions: Dict<SymbolId, MirFunction> = {}
functions[caller.symbol] = caller
functions[writer.symbol] = writer
val module = MirModule(name: "effect_module", functions: functions,
    statics: {}, constants: {}, types: {})
val vir = verification_ir_module_from_canonical_mir_v1(
    module, "source", "expanded", "woven", "policy")
expect(vir.closure_ready()).to_equal(true)
expect(vir.functions[1].called_symbols).to_equal([
    SymbolId(id: 8801)])
expect(vir.functions[1].effects).to_equal([
    VerificationEffectV1.Write("global:77")])
expect(vir.effect_closure_hash == "").to_equal(false)
```

</details>

### REQ-FV2-013 REQ-FV2-016 and NFR-FV2-007: compiler validation and mutation rejection

#### should bind exact Result variant and payload translation to the runtime artifact

- should bind exact Result variant and payload translation to the runtime artifact
- Validate logical Result outcomes against tagged runtime observations
   - Expected: result.accepted is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should bind exact Result variant and payload translation to the runtime artifact")
step("Validate logical Result outcomes against tagged runtime observations")
val result = validate_result_abi_translation_v1(7, "runtime-hash", [
    ResultAbiObservationV1(ResultSemanticOutcomeV1.Normal(41),
        ResultTaggedHandleProjectionV1(7, 0, 41)),
    ResultAbiObservationV1(ResultSemanticOutcomeV1.Error(-9),
        ResultTaggedHandleProjectionV1(7, 1, -9))
], "ResultTaggedAbi.validate_sound", "axiom-audit-hash", true)
expect(result.accepted).to_equal(true)
expect(result.certificate.unwrap().matches_edge(
    "result-tagged-abi-v1", result.source_semantic_hash,
    result.target_semantic_hash)).to_equal(true)
```

</details>

#### should certificate an accepted DCE edge against its semantic identities

- should certificate an accepted DCE edge against its semantic identities
- Validate the proved straight-line DCE fragment
   - Expected: result.accepted is true
   - Expected: result.certificate.unwrap().matches_edge("mir-dce-v1", source.semantic_hash(), target.semantic_hash()) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should certificate an accepted DCE edge against its semantic identities")
step("Validate the proved straight-line DCE fragment")
val source = fv2_dce_source()
val target = dce_tv_optimize(source)
val result = validate_dce_translation_v1(source, target, "MirDceTv.validate_sound:propext")
expect(result.accepted).to_equal(true)
expect(result.certificate.unwrap().matches_edge("mir-dce-v1", source.semantic_hash(), target.semantic_hash())).to_equal(true)
```

</details>

#### should reject an intentionally unsound live-value rewrite

- should reject an intentionally unsound live-value rewrite
- Mutate an operand-producing constant
   - Expected: result.accepted is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should reject an intentionally unsound live-value rewrite")
step("Mutate an operand-producing constant")
val source = fv2_dce_source()
val mutant = DceTvProgramV1([
    DceTvInstructionV1.Const(1, 20),
    DceTvInstructionV1.Const(2, 23),
    DceTvInstructionV1.Add(0, 1, 2)
], 0)
val result = validate_dce_translation_v1(source, mutant, "MirDceTv.validate_sound:propext")
expect(result.accepted).to_equal(false)
expect(result.diagnostic).to_contain("REJECTED")
```

</details>

#### should reject compiler evidence without the theorem trust audit

- should reject compiler evidence without the theorem trust audit
- Remove the transitive axiom evidence
   - Expected: result.accepted is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should reject compiler evidence without the theorem trust audit")
step("Remove the transitive axiom evidence")
val source = fv2_dce_source()
val result = validate_dce_translation_v1(source, dce_tv_optimize(source), "")
expect(result.accepted).to_equal(false)
expect(result.diagnostic).to_contain("AUDIT")
```

</details>

### REQ-FV2-017: dynamic verified composition

#### should admit an exact signed component with closed obligations

- should admit an exact signed component with closed obligations
- Validate plugin composition evidence
   - Expected: decision.closed_verification is true
   - Expected: decision.status equals `FormalStatus.ArtifactVerified`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should admit an exact signed component with closed obligations")
step("Validate plugin composition evidence")
val component = fv2_plugin()
val signature = SignatureVerificationReceiptV1(component.hash(), "release-key", "signature-checker", "evidence", true)
val policy = DynamicCompositionPolicyV1("interface", "verified", "compiler", ["release-key"])
val obligation = CompositionObligationV1("compose", "proposition", "certificate", true)
val decision = verify_dynamic_composition_v1(policy, component, signature, [obligation])
expect(decision.closed_verification).to_equal(true)
expect(decision.status).to_equal(FormalStatus.ArtifactVerified)
```

</details>

#### should reject a stale signed receipt or profile downgrade

- should reject a stale signed receipt or profile downgrade
- Mutate plugin identity and profile evidence
   - Expected: decision.admitted is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should reject a stale signed receipt or profile downgrade")
step("Mutate plugin identity and profile evidence")
val component = fv2_plugin()
val stale = SignatureVerificationReceiptV1("stale", "release-key", "signature-checker", "evidence", true)
val policy = DynamicCompositionPolicyV1("interface", "verified", "compiler", ["release-key"])
val obligation = CompositionObligationV1("compose", "proposition", "certificate", true)
val decision = verify_dynamic_composition_v1(policy, component, stale, [obligation])
expect(decision.admitted).to_equal(false)
expect(decision.diagnostic).to_contain("SIGNATURE-BINDING")
```

</details>

#### should keep an isolated unclosed plugin visible as bounded TCB

- should keep an isolated unclosed plugin visible as bounded TCB
- Declare rather than conceal the trusted boundary
   - Expected: decision.closed_verification is false
   - Expected: decision.status equals `FormalStatus.TrustedBoundary`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should keep an isolated unclosed plugin visible as bounded TCB")
step("Declare rather than conceal the trusted boundary")
val decision = declare_dynamic_bounded_tcb_v1(fv2_plugin(), "trust-manifest")
expect(decision.closed_verification).to_equal(false)
expect(decision.status).to_equal(FormalStatus.TrustedBoundary)
```

</details>

### REQ-FV2-018: existing external proof channel

#### should expand one retained proof uses root over the exact VC closure

- should expand one retained proof uses root over the exact VC closure
- Bind the existing proof channel to all thirteen canonical proposition identities
   - Expected: manifest.closed() is true
   - Expected: manifest.bindings.len() equals `13`


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should expand one retained proof uses root over the exact VC closure")
step("Bind the existing proof channel to all thirteen canonical proposition identities")
val trust = TrustManifestV1(["propext"], [], [], [], [], [])
val closure = generate_verification_obligation_closure_from_canonical_mir_v1(
    fv2_canonical_vc_function(), "woven-global-writer", "lean4",
    "lean-backend-v1", trust)
val manifest = generate_proof_uses_closure_manifest_v1(closure,
    "GlobalWriter.correct")
expect(manifest.closed()).to_equal(true)
expect(manifest.bindings.len()).to_equal(13)
expect(manifest.bindings[5].external_theorem).to_equal(
    "GlobalWriter.correct")
expect(manifest.bindings[12].external_theorem).to_equal(
    "GlobalWriter.correct_trust_closure")
```

</details>

### REQ-FV2-014: first SimpleOS implementation refinement slice

#### should exhaust the complete capability-rights product domain

- should exhaust the complete capability-rights product domain
- Validate real SimpleOS rights enforcement against its independent specification
   - Expected: receipt.checked_case_count equals `CAPABILITY_RIGHTS_CASE_COUNT_V1`
   - Expected: receipt.counterexample_count equals `0`
   - Expected: receipt.status equals `FormalStatus.ModelProven`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should exhaust the complete capability-rights product domain")
step("Validate real SimpleOS rights enforcement against its independent specification")
val receipt = validate_simpleos_capability_rights_refinement_v1(fv2_simpleos_axiom_report())
expect(receipt.checked_case_count).to_equal(CAPABILITY_RIGHTS_CASE_COUNT_V1)
expect(receipt.counterexample_count).to_equal(0)
expect(receipt.status).to_equal(FormalStatus.ModelProven)
```

</details>

#### should demonstrate specification sensitivity with a non-equivalent mutant

- should demonstrate specification sensitivity with a non-equivalent mutant
- Inspect mutation counterexamples


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should demonstrate specification sensitivity with a non-equivalent mutant")
step("Inspect mutation counterexamples")
val receipt = validate_simpleos_capability_rights_refinement_v1(fv2_simpleos_axiom_report())
expect(receipt.mutant_counterexample_count).to_be_greater_than(0)
```

</details>

#### should require typed replay-bound proof evidence for source promotion

- should require typed replay-bound proof evidence for source promotion
- Promote the model/product comparison through exact typed proof evidence


<details>
<summary>Executable SSpec</summary>

Runnable source: 19 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should require typed replay-bound proof evidence for source promotion")
step("Promote the model/product comparison through exact typed proof evidence")
val model = validate_simpleos_capability_rights_refinement_v1(fv2_simpleos_axiom_report())
val replay = close_independent_replay_v1(
    fv2_capability_replay_checker(ReplayCheckerClassV1.FreshLeanKernel),
    fv2_capability_replay_checker(ReplayCheckerClassV1.IndependentKernel))
val proof = ProofReceiptV1(
    model.model_theorem_root, FormalStatus.ModelProven, "cache",
    sha256_text("kernel-capabilities-olean"), [
        "fv2-simpleos-source-semantics:" + model.source_semantics_hash,
        "fv2-simpleos-model-semantics:" + model.model_semantics_hash],
    assurance_text_hash(fv2_simpleos_axiom_report()),
    model.trust_manifest_hash, "", replay.hash())
val receipt = promote_simpleos_capability_rights_refinement_v2(
    model, proof, replay)
expect(receipt.permits_source_refinement(
    capability_rights_verification_cache_key_v1())).to_be(true)
expect(receipt.status.permits_verified_release()).to_be(false)
```

</details>

#### should bind green-task completion to the real first-write-wins transition

- should bind green-task completion to the real first-write-wins transition
- Check every declared lifecycle/result boundary case
   - Expected: receipt.counterexample_count equals `0`
   - Expected: receipt.status equals `FormalStatus.ModelProven`


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should bind green-task completion to the real first-write-wins transition")
step("Check every declared lifecycle/result boundary case")
val receipt = validate_simpleos_green_task_complete_refinement_v1(
    fv2_scheduler_axiom_report())
expect(receipt.checked_case_count).to_equal(
    GREEN_TASK_COMPLETE_CASE_COUNT_V1)
expect(receipt.counterexample_count).to_equal(0)
expect(receipt.status).to_equal(FormalStatus.ModelProven)
expect(receipt.permits_model_evidence(
    green_task_complete_verification_cache_key_v1())).to_be(true)
expect(receipt.permits_source_refinement(
    green_task_complete_verification_cache_key_v1())).to_be(false)
```

</details>

#### should detect stale park metadata and double-complete overwrite mutants

- should detect stale park metadata and double-complete overwrite mutants
- Mutate both terminal lifecycle guarantees


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should detect stale park metadata and double-complete overwrite mutants")
step("Mutate both terminal lifecycle guarantees")
val receipt = validate_simpleos_green_task_complete_refinement_v1(
    fv2_scheduler_axiom_report())
expect(receipt.preserve_reason_mutant_counterexamples).to_be_greater_than(0)
expect(receipt.overwrite_done_mutant_counterexamples).to_be_greater_than(0)
```

</details>

#### should require the scheduler composite root and replay closure for source refinement

- should require the scheduler composite root and replay closure for source refinement
- Promote completion semantics through exact typed scheduler evidence
   - Expected: receipt.status equals `FormalStatus.SourceRefined`


<details>
<summary>Executable SSpec</summary>

Runnable source: 20 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should require the scheduler composite root and replay closure for source refinement")
step("Promote completion semantics through exact typed scheduler evidence")
val model = validate_simpleos_green_task_complete_refinement_v1(
    fv2_scheduler_axiom_report())
val replay = close_independent_replay_v1(
    fv2_scheduler_replay_checker(ReplayCheckerClassV1.FreshLeanKernel),
    fv2_scheduler_replay_checker(ReplayCheckerClassV1.IndependentKernel))
val proof = ProofReceiptV1(model.theorem_roots[0],
    FormalStatus.ModelProven, "cache", sha256_text("scheduler-olean"), [
        "fv2-simpleos-source-semantics:" + model.source_semantics_hash,
        "fv2-simpleos-model-semantics:" + model.model_semantics_hash],
    assurance_text_hash(fv2_scheduler_axiom_report()),
    model.trust_manifest_hash, "", replay.hash())
val receipt = promote_simpleos_green_task_complete_refinement_v2(
    model, proof, replay)
expect(receipt.status).to_equal(FormalStatus.SourceRefined)
expect(receipt.permits_source_refinement(
    green_task_complete_verification_cache_key_v1())).to_be(true)
expect(receipt.status.permits_verified_release()).to_be(false)
```

</details>

#### should keep the bounded scheduler slice below release verification

- should keep the bounded scheduler slice below release verification
- Inspect the exact bounded SymbolId and status ceiling


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should keep the bounded scheduler slice below release verification")
step("Inspect the exact bounded SymbolId and status ceiling")
val receipt = validate_simpleos_green_task_complete_refinement_v1(
    fv2_scheduler_axiom_report())
expect(receipt.symbol_id).to_contain("@bounded-state-result-v1")
expect(receipt.status.permits_verified_release()).to_be(false)
```

</details>

#### should close IPC while preserving buffers and waking exact waiters

- should close IPC while preserving buffers and waking exact waiters
- Validate the real green-channel close/drain transition
   - Expected: receipt.counterexample_count equals `0`
   - Expected: receipt.idempotence_counterexamples equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should close IPC while preserving buffers and waking exact waiters")
step("Validate the real green-channel close/drain transition")
val receipt = validate_simpleos_green_channel_close_refinement_v1(
    fv2_channel_close_axiom_report())
expect(receipt.checked_case_count).to_equal(
    GREEN_CHANNEL_CLOSE_CASE_COUNT_V1)
expect(receipt.counterexample_count).to_equal(0)
expect(receipt.idempotence_counterexamples).to_equal(0)
expect(receipt.permits_model_evidence(
    green_channel_close_cache_key_v1())).to_be(true)
expect(receipt.permits_source_refinement(
    green_channel_close_cache_key_v1())).to_be(false)
```

</details>

#### should detect lost buffered IPC and lost receiver wakeups

- should detect lost buffered IPC and lost receiver wakeups
- Mutate both close/drain preservation guarantees


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should detect lost buffered IPC and lost receiver wakeups")
step("Mutate both close/drain preservation guarantees")
val receipt = validate_simpleos_green_channel_close_refinement_v1(
    fv2_channel_close_axiom_report())
expect(receipt.dropped_buffer_mutant_counterexamples).to_be_greater_than(0)
expect(receipt.dropped_waiter_mutant_counterexamples).to_be_greater_than(0)
```

</details>

#### should require the IPC composite root and replay closure for source refinement

- should require the IPC composite root and replay closure for source refinement
- Promote close/drain semantics through exact typed IPC evidence
   - Expected: receipt.status equals `FormalStatus.SourceRefined`


<details>
<summary>Executable SSpec</summary>

Runnable source: 20 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should require the IPC composite root and replay closure for source refinement")
step("Promote close/drain semantics through exact typed IPC evidence")
val model = validate_simpleos_green_channel_close_refinement_v1(
    fv2_channel_close_axiom_report())
val replay = close_independent_replay_v1(
    fv2_channel_replay_checker(ReplayCheckerClassV1.FreshLeanKernel),
    fv2_channel_replay_checker(ReplayCheckerClassV1.IndependentKernel))
val proof = ProofReceiptV1(model.theorem_roots[0],
    FormalStatus.ModelProven, "cache", sha256_text("channel-olean"), [
        "fv2-simpleos-source-semantics:" + model.semantic_hash,
        "fv2-simpleos-model-semantics:" + model.model_semantics_hash],
    assurance_text_hash(fv2_channel_close_axiom_report()),
    model.trust_manifest_hash, "", replay.hash())
val receipt = promote_simpleos_green_channel_close_refinement_v2(
    model, proof, replay)
expect(receipt.status).to_equal(FormalStatus.SourceRefined)
expect(receipt.permits_source_refinement(
    green_channel_close_cache_key_v1())).to_be(true)
expect(receipt.status.permits_verified_release()).to_be(false)
```

</details>

#### should expose the IPC model boundary and status ceiling

- should expose the IPC model boundary and status ceiling
- Keep the bounded exact bridge distinct from the older broad abstraction
   - Expected: receipt.status equals `FormalStatus.ModelProven`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should expose the IPC model boundary and status ceiling")
step("Keep the bounded exact bridge distinct from the older broad abstraction")
val receipt = validate_simpleos_green_channel_close_refinement_v1(
    fv2_channel_close_axiom_report())
expect(receipt.symbol_id).to_contain("@bounded-v1")
expect(receipt.status).to_equal(FormalStatus.ModelProven)
expect(receipt.status.permits_verified_release()).to_be(false)
```

</details>

#### should make DBFS commit visibility conditional on durable WAL

- should make DBFS commit visibility conditional on durable WAL
- Execute the real commit boundary before and after WAL durability
   - Expected: receipt.checked_case_count equals `DBFS_COMMIT_CASE_COUNT_V1`
   - Expected: receipt.counterexample_count equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should make DBFS commit visibility conditional on durable WAL")
step("Execute the real commit boundary before and after WAL durability")
val receipt = validate_simpleos_dbfs_commit_refinement_v1(
    fv2_dbfs_axiom_report())
expect(receipt.checked_case_count).to_equal(DBFS_COMMIT_CASE_COUNT_V1)
expect(receipt.counterexample_count).to_equal(0)
expect(receipt.permits_model_evidence(
    dbfs_commit_cache_key_v1())).to_be(true)
expect(receipt.permits_source_refinement(
    dbfs_commit_cache_key_v1())).to_be(false)
```

</details>

#### should detect a commit-before-flush crash-visibility mutant

- should detect a commit-before-flush crash-visibility mutant
- Make an unflushed transaction incorrectly recoverable


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should detect a commit-before-flush crash-visibility mutant")
step("Make an unflushed transaction incorrectly recoverable")
val receipt = validate_simpleos_dbfs_commit_refinement_v1(
    fv2_dbfs_axiom_report())
expect(receipt.early_commit_mutant_counterexamples).to_be_greater_than(0)
```

</details>

#### should keep bounded crash refinement below artifact verification

- should keep bounded crash refinement below artifact verification
- Inspect the commit/crash SymbolId and status ceiling
   - Expected: receipt.status equals `FormalStatus.ModelProven`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should keep bounded crash refinement below artifact verification")
step("Inspect the commit/crash SymbolId and status ceiling")
val receipt = validate_simpleos_dbfs_commit_refinement_v1(
    fv2_dbfs_axiom_report())
expect(receipt.symbol_id).to_contain("@bounded-crash-v1")
expect(receipt.status).to_equal(FormalStatus.ModelProven)
expect(receipt.status.permits_verified_release()).to_be(false)
```

</details>

#### should require the DBFS composite root and replay closure for source refinement

- should require the DBFS composite root and replay closure for source refinement
- Promote commit/crash semantics through exact typed storage evidence
   - Expected: receipt.status equals `FormalStatus.SourceRefined`


<details>
<summary>Executable SSpec</summary>

Runnable source: 20 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should require the DBFS composite root and replay closure for source refinement")
step("Promote commit/crash semantics through exact typed storage evidence")
val model = validate_simpleos_dbfs_commit_refinement_v1(
    fv2_dbfs_axiom_report())
val replay = close_independent_replay_v1(
    fv2_dbfs_replay_checker(ReplayCheckerClassV1.FreshLeanKernel),
    fv2_dbfs_replay_checker(ReplayCheckerClassV1.IndependentKernel))
val proof = ProofReceiptV1(model.theorem_roots[0],
    FormalStatus.ModelProven, "cache", sha256_text("dbfs-olean"), [
        "fv2-simpleos-source-semantics:" + model.semantic_hash,
        "fv2-simpleos-model-semantics:" + model.model_semantics_hash],
    assurance_text_hash(fv2_dbfs_axiom_report()),
    model.trust_manifest_hash, "", replay.hash())
val receipt = promote_simpleos_dbfs_commit_refinement_v2(
    model, proof, replay)
expect(receipt.status).to_equal(FormalStatus.SourceRefined)
expect(receipt.permits_source_refinement(
    dbfs_commit_cache_key_v1())).to_be(true)
expect(receipt.status.permits_verified_release()).to_be(false)
```

</details>

#### should refine real shared unmap reference and writeback transitions

- should refine real shared unmap reference and writeback transitions
- Execute survivor last-dirty repeated and private one-page unmaps
   - Expected: receipt.checked_case_count equals `SHARED_UNMAP_CASE_COUNT_V1`
   - Expected: receipt.counterexample_count equals `0`
   - Expected: receipt.killed_mutant_count equals `4`


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should refine real shared unmap reference and writeback transitions")
step("Execute survivor last-dirty repeated and private one-page unmaps")
val receipt = validate_simpleos_shared_unmap_refinement_v1(
    fv2_shared_unmap_axiom_report())
expect(receipt.checked_case_count).to_equal(SHARED_UNMAP_CASE_COUNT_V1)
expect(receipt.counterexample_count).to_equal(0)
expect(receipt.killed_mutant_count).to_equal(4)
expect(receipt.permits_model_evidence(
    shared_unmap_cache_key_v1())).to_be(true)
expect(receipt.permits_source_refinement(
    shared_unmap_cache_key_v1())).to_be(false)
```

</details>

#### should keep bounded shared unmap evidence below artifact verification

- should keep bounded shared unmap evidence below artifact verification
- Inspect the one-page SymbolId and status ceiling
   - Expected: receipt.status equals `FormalStatus.ModelProven`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should keep bounded shared unmap evidence below artifact verification")
step("Inspect the one-page SymbolId and status ceiling")
val receipt = validate_simpleos_shared_unmap_refinement_v1(
    fv2_shared_unmap_axiom_report())
expect(receipt.symbol_id).to_contain("@bounded-one-page-v1")
expect(receipt.status).to_equal(FormalStatus.ModelProven)
expect(receipt.status.permits_verified_release()).to_be(false)
```

</details>

#### should require the shared-unmap composite root and replay closure for source refinement

- should require the shared-unmap composite root and replay closure for source refinement
- Promote unmap semantics through exact typed memory evidence
   - Expected: receipt.status equals `FormalStatus.SourceRefined`


<details>
<summary>Executable SSpec</summary>

Runnable source: 20 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should require the shared-unmap composite root and replay closure for source refinement")
step("Promote unmap semantics through exact typed memory evidence")
val model = validate_simpleos_shared_unmap_refinement_v1(
    fv2_shared_unmap_axiom_report())
val replay = close_independent_replay_v1(
    fv2_unmap_replay_checker(ReplayCheckerClassV1.FreshLeanKernel),
    fv2_unmap_replay_checker(ReplayCheckerClassV1.IndependentKernel))
val proof = ProofReceiptV1(model.theorem_roots[0],
    FormalStatus.ModelProven, "cache", sha256_text("unmap-olean"), [
        "fv2-simpleos-source-semantics:" + model.semantic_hash,
        "fv2-simpleos-model-semantics:" + model.model_semantics_hash],
    assurance_text_hash(fv2_shared_unmap_axiom_report()),
    model.trust_manifest_hash, "", replay.hash())
val receipt = promote_simpleos_shared_unmap_refinement_v2(
    model, proof, replay)
expect(receipt.status).to_equal(FormalStatus.SourceRefined)
expect(receipt.permits_source_refinement(
    shared_unmap_cache_key_v1())).to_be(true)
expect(receipt.status.permits_verified_release()).to_be(false)
```

</details>

#### should execute the scheduler-owned child wait exit and reap chain

- should execute the scheduler-owned child wait exit and reap chain
- Validate live wait zombie publication exact status collection and no double reap
   - Expected: receipt.checked_case_count equals `PROCESS_WAIT_CASE_COUNT_V1`
   - Expected: receipt.counterexample_count equals `0`
   - Expected: receipt.killed_mutant_count equals `4`


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should execute the scheduler-owned child wait exit and reap chain")
step("Validate live wait zombie publication exact status collection and no double reap")
val receipt = validate_simpleos_process_wait_refinement_v1(
    fv2_process_axiom_report())
expect(receipt.checked_case_count).to_equal(PROCESS_WAIT_CASE_COUNT_V1)
expect(receipt.counterexample_count).to_equal(0)
expect(receipt.killed_mutant_count).to_equal(4)
expect(receipt.permits_model_evidence(
    process_wait_cache_key_v1())).to_be(true)
expect(receipt.permits_source_refinement(
    process_wait_cache_key_v1())).to_be(false)
```

</details>

#### should require exact process proof and replay closure for source refinement

- should require exact process proof and replay closure for source refinement
- Promote the process chain through its exact composite theorem
   - Expected: receipt.status equals `FormalStatus.SourceRefined`


<details>
<summary>Executable SSpec</summary>

Runnable source: 20 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should require exact process proof and replay closure for source refinement")
step("Promote the process chain through its exact composite theorem")
val model = validate_simpleos_process_wait_refinement_v1(
    fv2_process_axiom_report())
val replay = close_independent_replay_v1(
    fv2_process_replay_checker(ReplayCheckerClassV1.FreshLeanKernel),
    fv2_process_replay_checker(ReplayCheckerClassV1.IndependentKernel))
val proof = ProofReceiptV1(model.theorem_root,
    FormalStatus.ModelProven, "cache", sha256_text("process-olean"), [
        "fv2-simpleos-source-semantics:" + model.source_semantics_hash,
        "fv2-simpleos-model-semantics:" + model.model_semantics_hash],
    assurance_text_hash(fv2_process_axiom_report()),
    model.trust_manifest_hash, "", replay.hash())
val receipt = promote_simpleos_process_wait_refinement_v2(
    model, proof, replay)
expect(receipt.status).to_equal(FormalStatus.SourceRefined)
expect(receipt.permits_source_refinement(
    process_wait_cache_key_v1())).to_be(true)
expect(receipt.status.permits_verified_release()).to_be(false)
```

</details>

#### should refine the real bounded process queue send and receive path

- should refine the real bounded process queue send and receive path
- Execute FIFO handle transfer backpressure close drain EOF and stale generation rejection
   - Expected: receipt.checked_case_count equals `PROCESS_QUEUE_CASE_COUNT_V1`
   - Expected: receipt.counterexample_count equals `0`
   - Expected: receipt.killed_mutant_count equals `4`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should refine the real bounded process queue send and receive path")
step("Execute FIFO handle transfer backpressure close drain EOF and stale generation rejection")
val receipt = validate_simpleos_process_queue_refinement_v1(
    fv2_process_queue_axiom_report())
expect(receipt.checked_case_count).to_equal(PROCESS_QUEUE_CASE_COUNT_V1)
expect(receipt.counterexample_count).to_equal(0)
expect(receipt.killed_mutant_count).to_equal(4)
expect(receipt.permits_model_evidence(
    process_queue_cache_key_v1())).to_be(true)
```

</details>

#### should require exact process-queue proof and replay closure for source refinement

- should require exact process-queue proof and replay closure for source refinement
- Promote process-queue semantics through its exact composite theorem
   - Expected: receipt.status equals `FormalStatus.SourceRefined`


<details>
<summary>Executable SSpec</summary>

Runnable source: 20 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should require exact process-queue proof and replay closure for source refinement")
step("Promote process-queue semantics through its exact composite theorem")
val model = validate_simpleos_process_queue_refinement_v1(
    fv2_process_queue_axiom_report())
val replay = close_independent_replay_v1(
    fv2_process_queue_replay_checker(ReplayCheckerClassV1.FreshLeanKernel),
    fv2_process_queue_replay_checker(ReplayCheckerClassV1.IndependentKernel))
val proof = ProofReceiptV1(model.theorem_root,
    FormalStatus.ModelProven, "cache", sha256_text("queue-olean"), [
        "fv2-simpleos-source-semantics:" + model.source_semantics_hash,
        "fv2-simpleos-model-semantics:" + model.model_semantics_hash],
    assurance_text_hash(fv2_process_queue_axiom_report()),
    model.trust_manifest_hash, "", replay.hash())
val receipt = promote_simpleos_process_queue_refinement_v2(
    model, proof, replay)
expect(receipt.status).to_equal(FormalStatus.SourceRefined)
expect(receipt.permits_source_refinement(
    process_queue_cache_key_v1())).to_be(true)
expect(receipt.status.permits_verified_release()).to_be(false)
```

</details>

### REQ-FV2-015: first generated RV32I instruction slice

#### should emit one closed ADD provider-to-retirement product from typed HWIR

- should emit one closed ADD provider-to-retirement product from typed HWIR
- Generate the bounded RV32 ADD product through strict HWIR
   - Expected: product.diagnostic() equals ``
   - Expected: product.rvfi_contract_sha256.len() equals `64`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should emit one closed ADD provider-to-retirement product from typed HWIR")
step("Generate the bounded RV32 ADD product through strict HWIR")
val product = compile_strict_rv32_add_rvfi_product(
    "fv2_rv32_add", 0x002081B3)
expect(product.diagnostic()).to_equal("")
expect(product.emitted.vhdl).to_contain("provider: entity work.fv2_rv32_add_provider")
expect(product.emitted.vhdl).to_contain("retirement_owner: entity work.fv2_rv32_add_retirement")
expect(product.emitted.vhdl).to_contain("retire_original_instruction=>rvfi_insn")
expect(product.rvfi_contract_sha256.len()).to_equal(64)
```

</details>

#### should fail closed when the requested instruction needs the unimplemented LSU

- should fail closed when the requested instruction needs the unimplemented LSU
- Attempt to generate a load through the disabled LSU seam
   - Expected: result.is_success() is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should fail closed when the requested instruction needs the unimplemented LSU")
step("Attempt to generate a load through the disabled LSU seam")
val result = compile_strict_riscv_scalar_product("fv2_rv32_load",
    CoreConfig.rv32_zca_mission_critical(), 0x00012083,
    LsuConfig.rv32_product_default())
expect(result.is_success()).to_equal(false)
expect(result.diagnostic).to_contain("LSU remains a disabled seam")
```

</details>

#### should not turn typed RTL emission into a verified-release claim

- should not turn typed RTL emission into a verified-release claim
- Keep proof, RVFI, synthesis, and netlist gates explicit
   - Expected: result.uses_legacy_fallback() is false
   - Expected: FormalStatus.ModelProven.permits_verified_release() is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should not turn typed RTL emission into a verified-release claim")
step("Keep proof, RVFI, synthesis, and netlist gates explicit")
val result = compile_strict_riscv_scalar_product("fv2_rv32_add_truth",
    CoreConfig.rv32_zca_mission_critical(), 0x002081B3,
    LsuConfig.rv32_product_default())
expect(result.uses_legacy_fallback()).to_equal(false)
expect(FormalStatus.ModelProven.permits_verified_release()).to_equal(false)
```

</details>

#### should keep constructed proof protocol receipts below executed evidence

- should keep constructed proof protocol receipts below executed evidence
- Validate exact job bindings without claiming external execution
   - Expected: receipt.status equals `FormalStatus.Specified`
   - Expected: receipt.evidence_receipt_hashes.len() equals `3`
   - Expected: receipt.permits_verified_release() is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 19 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should keep constructed proof protocol receipts below executed evidence")
step("Validate exact job bindings without claiming external execution")
val artifacts = generate_rv32_add_formal_artifacts(
    "fv2_rv32_add_evidence", 0x002081B3).ok().unwrap()
val prove = riscv_formal_job_receipt_v1("rv32i.add.prove",
    artifacts.prove_sby, "PASS", "sby/yosys/boolector",
    RiscvFormalJobStatusV1.Proved)
val cover = riscv_formal_job_receipt_v1("rv32i.add.cover",
    artifacts.cover_sby, "PASS reached", "sby/yosys/boolector",
    RiscvFormalJobStatusV1.Covered)
val mutant = riscv_formal_job_receipt_v1("rv32i.add.mutant",
    artifacts.mutant_sby, "FAIL counterexample", "sby/yosys/boolector",
    RiscvFormalJobStatusV1.Counterexample)
val receipt = reduce_rv32_add_formal_evidence(
    artifacts, prove, cover, mutant)
expect(receipt.status).to_equal(FormalStatus.Specified)
expect(receipt.evidence_receipt_hashes.len()).to_equal(3)
expect(receipt.permits_verified_release()).to_equal(false)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 81 |
| Active scenarios | 81 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-SYSTEM`
- `REQ-FV2-001`
- `REQ-FV2-019`
- `REQ-FV2-020`
- `REQ-FV2-004`
- `REQ-FV2-002`
- `REQ-FV2-006`
- `REQ-FV2-007`
- `REQ-FV2-003`
- `REQ-FV2-005`
- `REQ-FV2-008`
- `REQ-FV2-009`
- `REQ-FV2-010`
- `REQ-FV2-011`
- `REQ-FV2-012`
- `REQ-FV2-013`
- `REQ-FV2-016`
- `REQ-FV2-017`
- `REQ-FV2-018`
- `REQ-FV2-014`
- `REQ-FV2-015`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `95259accbc23d94066ecfe4675d77bd2c33f490460b61b1d54cbea5c68661f7a`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `95259accbc23d94066ecfe4675d77bd2c33f490460b61b1d54cbea5c68661f7a`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `95259accbc23d94066ecfe4675d77bd2c33f490460b61b1d54cbea5c68661f7a`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **74/100**; effective score: **49/100**; blockers: **1**.

SSpec documentization score: 49/100
source: test/03_system/compiler/formal_verification_2_0_spec.spl
mirror: doc/06_spec/03_system/compiler/formal_verification_2_0_spec.md (current)
findings: 14 blockers: 1
  narrative=100 structure=60 oracle=70
  traceability=60 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
  raw=74; blocker cap makes effective=49
doc/06_spec/03_system/compiler/formal_verification_2_0_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/compiler/formal_verification_2_0_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, primary workflow, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/compiler/formal_verification_2_0_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 21 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/03_system/compiler/formal_verification_2_0_spec.spl:1:1: blocker SSDOC-TRC-003 [traceability] (-40): 20 declared requirement(s) have no scenario binding
  why: A requirement list without scenario evidence is inventory, not traceability.
  improve: Bind the stable requirement ID inside its executable scenario or explicit blocked case.
test/03_system/compiler/formal_verification_2_0_spec.spl:326:1: warning SSDOC-BEH-001 [structure] (-10): scenario 'should classify Lean-only success as model-proven' has no visible step flow
  why: Ordered visible actions make the manual operable.
  improve: Add ordered step("...") calls for meaningful actions.
test/03_system/compiler/formal_verification_2_0_spec.spl:326:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should classify Lean-only success as model-proven' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/03_system/compiler/formal_verification_2_0_spec.spl:355:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should reserve release permission for artifact verification' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/03_system/compiler/formal_verification_2_0_spec.spl:355:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should reserve release permission for artifact verification' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/compiler/formal_verification_2_0_spec.spl:363:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should reject a claimed artifact receipt with missing refinement evidence' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/03_system/compiler/formal_verification_2_0_spec.spl:363:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should reject a claimed artifact receipt with missing refinement evidence' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/compiler/formal_verification_2_0_spec.spl:372:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should accept only complete artifact-bound executed evidence' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/03_system/compiler/formal_verification_2_0_spec.spl:372:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should accept only complete artifact-bound executed evidence' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/compiler/formal_verification_2_0_spec.spl:386:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should reject unknown timeout missing-tool stale unsupported and environment failures' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/03_system/compiler/formal_verification_2_0_spec.spl:405:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should pin signer policy outside the caller-controlled CLI boundary' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
<!-- sspec-maintain:scorecard:end -->
