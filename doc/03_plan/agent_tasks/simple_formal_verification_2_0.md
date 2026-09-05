<!-- codex-design -->
# Simple Formal Verification 2.0 Implementation Plan

**Status:** In implementation; foundations, seven bounded SimpleOS source-refinement slices, typed Gate 0–7 collectors, pinned replay tooling, and one independently replayed SimpleOS root exist; six closed-lane literal-boundary replays, effectful heap/global transition proofs, actual RV32/RV64 product evidence, authorized signing policy, and final self-hosted verification remain open
**Date:** 2026-08-12
**Merge owner:** Formal Verification 2.0 integration owner
**Final reviewer:** Best available normal/highest-capability reviewer independent of the production lanes

## Policy compatibility rule

The verified profile is a V2 assurance-policy interface. Do not add a fifth
case to frozen `AssuranceStrictness` or mutate `ResolvedAssurancePolicyV1`.
V1 consumers must conservatively enforce `verified` as `critical`; only the
V2 resolver and FV2 evidence consumers may retain `verified` and issue an
`APOLV2-*` identity. Work packages that ingest SDN, CLI, or child-process
profile data must preserve this distinction.

## 2026-08-12 verification environment status

- The clean composite admission at
  `/mnt/data/.simple/bootstrap/composite-forensic-admission2-20260812/output`
  compiled 835 units and linked candidate
  `f6e48bc8e878b1ad4b9abc9a29280fa80ba920f3059494ef7f4c7ea7c4e31df9`,
  but the mandatory Stage 2 sanity gate rejected and quarantined it. Both
  `--version` and unsupported-command probes exited 132 with
  `runtime error: invalid field receiver`; retained evidence reports
  `status=fail` and `admitted=no`. This artifact is diagnostic only.
- The independently owned `/mnt/data/bs2/perf-integrated-99518` Stage 2 build
  remains running and has not produced an executable candidate. Do not start a
  competing bootstrap or treat its partial cache as admission evidence.

- A guarded pure-Simple bootstrap at
  `/mnt/data/bs2/perf-integrated-50a996` reached Stage 2, then the 45-minute
  guard terminated it (`exit 143`). Its retained `stage2-native-build.log`
  reports 44 pre-existing full-compiler type-inference failures such as
  `struct 'ANY' field ...`; no `stage2-admitted/simple` was produced.
- The previously admitted pure-Simple compiler at
  `/mnt/data/.simple/bootstrap/authority-22d7/output/stage3/x86_64-unknown-linux-gnu/stage2-admitted/simple`
  traps with `runtime error: invalid field receiver` (`exit 132`) for both
  `compile` and `native-build`, including an unrelated known fixture. This is
  the already tracked struct-allocation/receiver-guard authority defect, not a
  focused FV2 diagnostic.
- Consequently the new focused specs have static diff/stub review and required
  direct-env guards (`--working` and `--staged`) passing, but no self-hosted
  compile/test PASS is claimed. The Rust seed was intentionally not substituted.

## Frozen boundary

Before parallel work, the merge owner freezes: `VerificationIR v1`, `SemanticCoverage v1`, `ProofObligation v1`, `ProofReceipt v1`, `TrustManifest v1`, `WeaveManifest v1`, `CompilerCertificate v1`, `HardwareProofReceipt v1`, `FormalStatus v1`, and `VerificationCacheKey v1`. An incompatible revision requires a version bump and migration test. Stateful semantic-authority fields therefore live in `ExecutionContractObligation v2`; v1 remains structurally unchanged and rejects clauses it cannot soundly represent.

## Ordered delivery

**Current FV-1/FV-3 integration hold:** `ResolvedDirectCallManifestV1`, `ResolvedCanonicalModuleClosureV2`, and `ResolvedVerificationIrModuleV2` now make direct-call, effect, and VIR closure fail closed against exact owner/callee `SymbolId` and signature snapshots. They are not yet emitted by the canonical frontend resolver. Until that producer is wired before VIR construction, ordinary source programs cannot enter the resolved V2 closure and cannot be promoted beyond model/source evidence. The bridge must preserve the module snapshot, resolver receipt, every direct call site, and the callee signature/body hashes; deriving these bindings from a textual callee name is prohibited.

The producer must also classify every direct call before MIR erases extern declarations: one resolver-originated internal SymbolId binding or one explicit external boundary carrying boundary, ABI, and effect-contract identities. Generated/runtime calls cannot be inferred from a post-MIR `rt_*` name and must fail closed until this tagged boundary extension exists.

| Wave | Work package | Deliverable | Depends on | Exit gate |
|---|---|---|---|---|
| 0 | FV-0 Truth audit | Status migration, dependency-aware proof roots, fail-closed trust/axiom audit | None | Gate 0 |
| 1 | FV-1 VIR | Canonical woven HIR-to-VIR, source maps, semantic hashes, coverage registry, resolver-produced direct-call manifest | FV-0 | Gate 1 foundation |
| 1 | FV-2 Exact Lean backend | Typed Lean IR and exact core type/expression lowering | FV-1 | Gate 1 |
| 2 | FV-3 Contracts/automation | Execution-linked contracts, invariants, termination, frame/effect VCs, classifier | FV-1/2 | Gate 2 proof frontend |
| 2 | FV-4 Trust/receipts | Receipts, manifests, fresh/independent replay, signing boundary | FV-0 | Gate 2 evidence |
| 2 | FV-5 AOP/macros | Canonical weave, exact manifest, ghost noninterference, monitor semantics | FV-1 | Gate 3 |
| 3 | FV-6 Compiler refinement | Translation validators and selected pass/backend certificates | FV-1/2/4 | Gate 2 closure |
| 3 | FV-9 Performance | Symbol/SCC DAG, semantic cache, scheduler, metrics | Frozen interfaces | Incremental budget met |
| 4 | FV-7 SimpleOS | First end-to-end kernel slice refinement and mapped concurrency traces | FV-1/3/4 | Gate 4 |
| 4 | FV-8 RISC-V | HWIR retirement semantics, generated RVFI, Sail/RVFI/equivalence chain | FV-1/4 | Gates 5–6 |
| continuous | FV-10 Adversarial tests | Vacuity, mutation, stale-cache, false-evidence tests; no production edits | All interfaces | Required at every gate |

### Resolver call-manifest migration interface

| NFR | Wave / owner | Required evidence | Status |
|---|---|---|---|
| NFR-FV2-001 reproducibility | 1, 3 / VIR and receipt owners | repeated semantic/certificate/receipt hashes from pinned inputs | Source/tests implemented; execution pending |
| NFR-FV2-002 sound failure | all / each lane owner | malformed, stale, timeout, unknown, missing-tool negatives | Source/tests implemented; execution pending |
| NFR-FV2-003 bounded trust | 3, 6 / trust owner | complete transitive trust manifest and axiom audit | Source/tests implemented; external audit pending |
| NFR-FV2-004 incrementality | 1, 3 / cache owner | SymbolId/SCC invalidation and formatting-only reuse | Source/tests implemented; metrics pending |
| NFR-FV2-005 determinism | 1–3 / producer owners | byte-stable VIR, Lean IR, weave, receipts | Source/tests implemented; repeat-run evidence pending |
| NFR-FV2-006 performance | 3, 6 / tooling owner | warm latency, cache metrics, max RSS, no repeated scans | Blocked by unavailable self-hosted CLI |
| NFR-FV2-007 diagnostics | all / lane owners | source/SymbolId/value/effect/signal mapping | Source/tests implemented; execution pending |
| NFR-FV2-008 evolvability | all / interface owner | V1 migration and stale-cache tests | Policy V1→V2 typed migration and focused tests implemented; execution pending |
| NFR-FV2-009 independence | 3, 5, 6 / replay and hardware owners | fresh Lean plus independent checker/oracle | Blocked |
| NFR-FV2-010 scalability | 3 / scheduler owner | bounded parallel DAG execution metrics | Bounded task executor and deterministic commit implemented; authoritative runtime metrics pending |

## First implementation wave — strict order

1. Replace existential/disconnected contract theorems with execution-linked obligations.
2. Audit transitive axioms/trust; replace output-text proof counting.
3. Introduce the truthful status lattice and migrate claims conservatively.
4. Freeze and implement VIR v1 plus exhaustive semantic coverage.
5. Replace machine `Int/Nat` lowering with exact bit-vector semantics.
6. Replace string-oriented Lean generation with typed Lean IR.
7. Unify AOP semantics and weave before VIR.
8. Bind proof, compiler, trust, weave, tool, and artifact identities into receipts/cache keys.
9. Refine one SimpleOS subsystem implementation to its model.
10. Generate the smallest real RV32I core and prove one instruction family end to end.

## Gate acceptance

| Artifact | Owner | State |
|---|---|---|
| `test/01_unit/compiler/mir/mir_coverage_opcode_admission_spec.spl` | MIR evidence owner | Present; current focused foundation |
| `doc/06_spec/01_unit/compiler/mir/mir_coverage_opcode_admission_spec.md` | MIR evidence owner + manual reviewer | Present; historical compatibility-liveness content from `8257fde9eb1` is accepted input |
| `test/03_system/compiler/formal_verification_2_0_spec.spl` | system-test owner | Present; 20 REQs, 10 NFRs, frozen steps/helpers, 81 examples |
| `doc/06_spec/03_system/compiler/formal_verification_2_0_spec.md` | docgen + merge owner | Present mirror; zero-stub regeneration blocked on Stage 4 runtime |
| `doc/03_plan/sys_test/simple_formal_verification_2_0.md` | system-test owner | Present in this lane; planning evidence only |
| research, requirements, architecture, detail design | research/design owners | Committed accepted artifacts; current implementation status refreshed in this plan |

Current FV-8 evidence: the bounded ADD proof/cover/killed-mutant receipt,
the pinned concrete Sail ADD differential receipt protocol, and
the RTL-to-synthesized-JSON equivalence receipt are implemented. The latter is
hash-bound to the exact generated RTL, module, synthesis policy, Yosys/GHDL
identities, netlist, and equivalence log and can reach only
`backend_refined`. Execution of the complete lane remains blocked by the
currently deployed Rust seed; the end-to-end wrapper deliberately exits 2
before generation. The Sail wrapper also independently exits 2 until a pinned
simulator and RV32 config are supplied. Executed ADD differential comparison,
HWIR-to-RTL semantic refinement beyond code-generation identity, RV64,
privilege/MMU, post-place-and-route/deployed identity, and Linux remain open.

Sail resume command:

```sh
sh scripts/setup/setup-fv2-sail-riscv.shs
# export the three paths printed by setup, then:
sh scripts/rtl/check-fv2-rv32-add-end-to-end.shs
```

The setup command acquires the already approved revision, requires Sail 0.20.1
or newer through the upstream build, disables test/GMP downloads, builds the
model and RV32 config, and emits a lock binding their hashes. Owner: FV-8
hardware formal lane. Final reviewer: FV2 merge owner/highest-capability model.

## Parallel-lane rules

**Recovery review status: source audit completed; overall acceptance
WARN/blocked.** The rebased delta has new trust-boundary fixes but no canonical
runtime execution. Earlier static review does not promote unavailable runtime
or external evidence.

Current continuation review lane: Codex Spark is `N/A` because this session does
not expose a Spark model. The merge owner retains review responsibility; this
does not waive the final independent highest-capability review.

### Recovery audit ledger (2026-08-15)

Closed in source, pending canonical execution: recursively dependency-bound
proof-DAG work identity, external schedule validation, and empty-graph
rejection; fail-closed scalar worker measurements; exact Wave 6
receipt multiplicity; verified cache-key identities; DCE SHA-256 certificate
identities; V9 input symlink and mutant-counterexample checks; and rejection of
caller-selected RV64 row authorities; reachable staged RV64 failure
classification; strict VIR function/module identity and membership checks;
fail-closed public replay/VC boundaries; caller-record execution-authority
rejection for Gates 0–3, 5, and 6; and a diagnostic-only public gate finalizer
for every non-Phase-4 gate.

Still blocked and not promoted: the resolved VIR V2 companion now binds an
exhaustive reachable `SemanticCoverageV1` manifest including every terminator,
and additive Wave 6 V2 routes it through the exact-core V2 collector. All
instruction and terminator variants remain truthfully `Unsupported`, and the
collector rejects caller-authored Exact rows until a canonical typed transition
manifest and resolved VIR V3 producer exist; frozen Wave 6 V1 remains unchanged.
`WeaveManifestV1` lacks its canonical
producer, so Gate 3 deliberately cannot pass; replay closure still needs
approved checker authority plus retained material receipts rather than
hash-only identities, so public assembly and V1 VC promotion deliberately
cannot pass; V9 now binds only its four exact RVFI/runtime properties and
explicitly excludes full-ISA, Zicsr, and Zifencei semantic conformance, but
executed solver evidence is still absent; the seven canonical RV64 authority wrappers/product
artifacts are incomplete; and Wave 6 has no release-admitted production call
site or repository-owned approved-signer policy. Gate 5 likewise lacks a
runner-owned SBY/equivalence/Sail assembly boundary. These are verification
blockers, not implicit Phase 4 work.

V2 signer-policy authority now uses the additive V3 schema and canonical
SHA-256 over the full resolved policy, flight rules, and sorted signer allow
list; legacy collision-prone `APOLV2-<decimal>` admission and the V1 CLI
downgrade are fail-closed. The fixed signer-policy spelling is regular/no-follow
checked, but every value reducer and CLI path remains deny-all until a trusted
install-root resolver and atomic no-follow snapshot issue provenance. The
tracked policy remains deny-all and no V3 signer provisioning is claimed.

### Recovery audit ledger (2026-08-15)

Closed in source, pending canonical execution: recursively dependency-bound
proof-DAG work identity, external schedule validation, and empty-graph
rejection; fail-closed scalar worker measurements; exact Wave 6
receipt multiplicity; verified cache-key identities; DCE SHA-256 certificate
identities; V9 input symlink and mutant-counterexample checks; and rejection of
caller-selected RV64 row authorities; reachable staged RV64 failure
classification; strict VIR function/module identity and membership checks;
fail-closed public replay/VC boundaries; caller-record execution-authority
rejection for Gates 0–3, 5, and 6; and a diagnostic-only public gate finalizer
for every non-Phase-4 gate.

Still blocked and not promoted: the resolved VIR V2 companion now binds an
exhaustive reachable `SemanticCoverageV1` manifest including every terminator,
and additive Wave 6 V2 routes it through the exact-core V2 collector. All
instruction and terminator variants remain truthfully `Unsupported`, and the
collector rejects caller-authored Exact rows until a canonical typed transition
manifest and resolved VIR V3 producer exist; frozen Wave 6 V1 remains unchanged.
`WeaveManifestV1` lacks its canonical
producer, so Gate 3 deliberately cannot pass; replay closure still needs
approved checker authority plus retained material receipts rather than
hash-only identities, so public assembly and V1 VC promotion deliberately
cannot pass; V9 now binds only its four exact RVFI/runtime properties and
explicitly excludes full-ISA, Zicsr, and Zifencei semantic conformance, but
executed solver evidence is still absent; the seven canonical RV64 authority wrappers/product
artifacts are incomplete; and Wave 6 has no release-admitted production call
site or repository-owned approved-signer policy. Gate 5 likewise lacks a
runner-owned SBY/equivalence/Sail assembly boundary. These are verification
blockers, not implicit Phase 4 work.

V2 signer-policy authority now uses the additive V3 schema and canonical
SHA-256 over the full resolved policy, flight rules, and sorted signer allow
list; legacy collision-prone `APOLV2-<decimal>` admission and the V1 CLI
downgrade are fail-closed. The fixed signer-policy spelling is regular/no-follow
checked, but every value reducer and CLI path remains deny-all until a trusted
install-root resolver and atomic no-follow snapshot issue provenance. The
tracked policy remains deny-all and no V3 signer provisioning is claimed.

### Temporary Stage 2/3 verification policy

The user authorized provisional compilation and test feedback from an available
Stage 2/3 artifact. Such runs must be labeled `PROVISIONAL`, retain the exact
binary hash and exit status, and may drive source fixes. They cannot check an
acceptance box, satisfy a pre-push/release gate, or produce PASS evidence.
TODO818 requires the unchanged final tree to be rerun with the source-matched
Stage 4 executable after TODO666/TODO667 complete.

The available provisional binary SHA-256
`04a38e21d6fbd86149d46d3ee2d761349f8ad29b02c5037a8eb589b6a1b9e4e0`
was attempted once for the RV64 runner check, its focused unit spec, and the
FV2 system spec. All three terminated with signal-derived exit 139. Hash-bound
logs are retained at `/tmp/restart12-fv2-provisional-{check,unit,system}.log`;
no criterion passed and these commands must not be repeated with that binary.

- `bin/simple` and the canonical deployed self-hosted binary are absent in this
  worktree. A stale/noncanonical ELF failure or Rust-seed success is not PASS.
- The latest receipt-authorized bounded recovery fixed the missing defer marker,
  imported the shared module-constant/callable/argv owners, and passed Stage 2
  plus sanity. Final cycle 3 reproduced a byte-identical Stage 3 exit 139 after
  the frontend error counter expanded from 1 to 25. No Stage 4 or FV2 runtime
  PASS is claimed. A fresh lane must surface the first hidden frontend
  diagnostic; do not start a fourth cycle in this one.
- Wave 5 RV64 has a seven-row owner wired directly to Gate 6 and now rejects
  caller-selected executables/policies. Several frozen authority wrappers are
  absent, so the owner intentionally fail-closes before execution. Exact kernel
  replay proofs, netlist/equivalence artifacts, Linux image, and pinned
  independent ISA-oracle inputs remain unavailable, so no Gate 6 PASS is
  claimed.
- Research, requirements, architecture, and design artifacts are committed.
  The system spec and manual mirror are present; authoritative SSpec/docgen
  execution remains blocked by the missing Stage 4 runtime.
- Each acceptance command runs at most once after PASS. Each gate has at most
  three fix/verify cycles; identical results stop and are reported.
- Final completion requires zero verification FAIL items, clean authoritative
  runtime gates, an intentional commit, serialized fetch/rebase/push without
  force or a branch, refetched reachability proof, clean detached worktree, and
  the required done marker. Incomplete predecessor gates remain unchecked.
