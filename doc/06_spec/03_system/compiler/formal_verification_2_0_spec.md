# Simple Formal Verification 2.0 — Foundation Gates

Status: modern executable SSpec restored and reconciled; standalone SPipe
regeneration remains blocked on the missing canonical pure-Simple test runtime.

This operator manual mirrors
`test/03_system/compiler/formal_verification_2_0_spec.spl`. It covers only the
implemented foundation gates and bounded SimpleOS refinement paths. It does not
claim externally executed independent replay, full product closure, generated
RV32I/RV64 proof, post-synthesis equivalence, or a verified release.

## Preconditions

- A genuine pure-Simple compiler/test runner, not the Rust bootstrap seed.
- Lean 4.33-compatible project tooling for transitive proof-root audits.
- Clean, retained inputs for receipt and semantic-hash comparison.

## Operator workflow

1. **Audit the formal claim boundary.** Resolve the `verified` assurance profile
   and confirm model, source, backend, and artifact states remain distinct.
2. **Construct canonical verification evidence.** Generate canonical semantics
   and inspect exact machine types, typed effects, contracts, and typed Lean.
3. **Reject stale or unsupported evidence.** Inspect retained contracts:
   predicates must be absent from the executable
   body, carry exact source locations, call the emitted function, and include a
   separate precondition-satisfiability root. Stateful VCs must name exact
   input-domain, reachability, transition, frame-region, recursive-call, and
   well-founded-order semantic authorities as applicable.
4. **Replay the shipped artifact independently.** Audit every declared proof
   root, require distinct checker identities over identical artifact bytes, and
   reject missing, hidden, native-trust, timeout, or stale dependencies.
5. Validate weave, cache, trust, compiler, replay, and artifact identities.
6. Validate the proved DCE fragment, including its before/after semantic hashes
   and transitive theorem audit.
7. Refuse release whenever the status, receipt, or concrete compiler
   certificate lacks an evidence edge.
8. Build `src/verification/kernel_capabilities` and require the
   `rights_allow9_sound` root to list only standard Lean logic axioms; native
   decision axioms are explicit failures.

## Covered scenarios

The executable spec names every `REQ-FV2-001` through `REQ-FV2-020` and every
`NFR-FV2-001` through `NFR-FV2-010`. Its shared fixtures are
`setup_fv2_fixture`, `check_fv2_gate`, and `check_fv2_replay`; each invokes a
real typed reducer and none is a placeholder.

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
  VC was executed. A separate unit-covered evidence
  closure accepts only thirteen exact, artifact/trust/replay-bound theorem
  receipts with complete DAG dependencies and remains `model_proven`.
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
  checksum, and every signed passed-gate receipt is rehashed from its exact
  fixed-root file before admission.
  Executed self-hosted test evidence remains pending.
- REQ-FV2-020: the frozen eight-stage delivery reducer preserves honest partial
  progress, rejects a pass that skips a blocked predecessor, and becomes ready
  only when every gate passes and the final verified-release decision is bound.
  Release-command orchestration is present; executed per-gate collectors remain
  pending. Signed evidence contains the canonical eight-gate manifest hash, and
  CLI admission rejects any gate/order/receipt mutation that does not match it.
  Gate 0 now has a typed collector over exact proof receipts, closed transitive
  axiom audits, and accepted fresh/independent replay closures for the same
  artifact. Gate 1 also has a typed collector over self-validating canonical
  VIR and five exact executed-check receipts. Gate 2 binds executed woven→VIR
  construction to an ordered,
  independently validated compiler-certificate chain ending at the exact
  artifact. Gate 3 binds exact macro/AOP manifests, woven VIR provenance,
  advice proof material, and a sealed dynamic-transform lock; the remaining
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

## Evidence and limitations

The executable source is the test oracle. This manual is not proof evidence.
The exact proof/checker commands and the uncovered requirement matrix live in
`doc/03_plan/sys_test/simple_formal_verification_2_0.md`. Until the pure-Simple
runner is restored, this mirror has not received a successful zero-stub
`spipe-docgen` receipt and must not be used to support `STATUS: PASS`.

## Executable specification

The complete executable source remains at:

`test/03_system/compiler/formal_verification_2_0_spec.spl`
