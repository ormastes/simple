# Agent plan: L7 three-payload bounded formal verification

## 2026-09-11 invariant-audit handoff

The [current source audit and proposed seven invariants](../../04_architecture/three_payload_compile_formal_verification.md#2026-09-11-three-file-and-invalidation-audit)
supersede any interpretation that the existing bounded roots prove ordinary
three-file compilation or sound end-to-end facet invalidation. They do not
replace the historical roots, execution receipts or cycle cap below.

| Work item | Required result | Current status |
|---|---|---|
| `FV-L7-I001` payload confinement | Eligible cold-two/warm-three attempted IO, separate control IO, no RR/fourth-input success | Partial broker; ordinary source loader still loads imports. |
| `FV-L7-I002` forward/RR coherence | Exact same-generation dual relation; authenticated complete old history including empty history | V1 nil-history gap; V2 productive authority closed. |
| `FV-L7-I003` affected closure | Old/new membership, absence and SCC closure for trait/aspect/macro changes | Authenticated domain authority unavailable. |
| `FV-L7-I004` exact reuse | Complete consumed body/signature/layout/scope facets; unchanged effective closure permits reuse | Legacy textual interface under-captures fields; positive semantic issuer unavailable. |
| `FV-L7-I005` publication | Durable complete candidate and commit-scoped lease guard before one active root switch; resolve lost acknowledgment/cancellation by durable commit identity | Host guard/publication activation closed. |
| `FV-L7-I006` conservative refusal | Missing/corrupt/Partial/Unknown cannot become empty affected set or cache hit | Refusal components exist; end-to-end proof OPEN. |
| `FV-L7-I007` coherent recovery | Recover one whole generation in durable commit order, never a mixed/prepared root or a losing publisher's stale pin | Model only; host crash/power-loss evidence OPEN. |

Root owns implementation/dependency allocation and merge. This audit's owner
is `/root/unified_plan_review_astra`; independent Astra source/claim review is
required. Lower-model sidecars: N/A for this bounded documentation audit.
Future source/model/spec owners must freeze new helper signatures and exact
paths before implementation; unchanged historical gates are not rerun here.
All seven obligations are OPEN/U, with no new completion or acceptance weight.
Qualify scenario-body execution explicitly; the old interpreter command below
must not be treated as executable coverage merely because it loads a file.

The later bounded implementation candidate authored partial contract/model
evidence for `I001`, `I002`, `I004`, `I005`, and `I007`. It does not change the
OPEN/U status: dependency provenance, live issuer/host authority, qualified
Lean and SSpec execution, and source refinement remain blocking.

## Frozen ownership

| Role | Agent/model | Owned paths | Status |
|---|---|---|---|
| Planner/architect | `/root/l7_formal_plan_astra` / Astra | frozen types, roots, steps, claims | complete |
| Implementation | `/root/l7_formal_sol` / Sol | additive Lean, verification leaf, fixtures, spec, docs | authored; gate unverified |
| Final formal/claim reviewer | Astra | exact proof roots, source-link claims, quarantine caveat | required |
| Merge owner | `/root` | shared integration and any later admission | pending |
| Lower-model sidecar | N/A | narrow fixed interfaces; no separable generated table lane used | reviewed N/A |

Production compiler/cache owners, availability flags, the shared optimization
plan, runtime admission, commits, and pushes are outside this lane.

## Work packages

| Package | Owner | Inputs | Acceptance | Open handoff |
|---|---|---|---|---|
| FV-L7-A model | Sol | Astra types and nine roots | all modules imported by Audit; no trust bypass | post-cap fixes require a fresh Lean gate |
| FV-L7-B source binding | Sol | current production paths | bounded real file reads bind current bytes/dependencies/model/checker/toolchain | source-to-VIR refinement |
| FV-L7-C replay | Sol | eleven frozen IDs | calls actual packer, semantic, broker, RR, journal and GC functions | admitted full CLI unavailable |
| FV-L7-D negative fixtures | Sol | frozen counterexamples | source mutation, RR replacement/mismatch, journal conflict/torn tail, stale epoch | mutation receipt unavailable |
| FV-L7-E review | Astra | exact final identities and gate output | reject overclaims; confirm theorem roots/axioms/caveats | pending |
| FV-L7-F merge | root | Astra verdict | additive integration only | pending |

## Gates

1. Lean proof integrity:
   `sh scripts/check/check-lean-proofs.shs --project src/verification/three_payload_compile verification/three_payload_compile`.
2. Retain all nine `#print axioms` outputs and pass them through
   `audit_lean_axiom_report`.
3. Run
   `<admitted-self-hosted-full-cli> test test/00_formal_verification/compiler/three_payload_compile_refinement_spec.spl --mode=interpreter`.
4. Recompute current source bindings during replay; stored labels are not
   evidence.
5. Astra independently reviews proof roots and claims before root merges.

Gate 1 initially stopped because `lake` was absent. The authorized official
Lean 4.30.0 AArch64 archive then matched its expected SHA-256, but three bounded
gate cycles ended at a record-update parse error. That expression has been
rewritten. Astra's later inspection also required an explicit derived
`LawfulBEq` instance for `RrEdge`; that correction is applied. Neither fix is
rerun in this session under the mandatory cycle cap. Gate 3 remains
unavailable: the full CLI is the Rust seed, the admitted Stage 2
artifact is compiler-only, and Stage 3 failed. Do not substitute those tools.

The current receipt builder is deliberately closed as `NotChecked`. Caller-
constructed bindings, matched observation DTOs, mismatched mutant DTOs, and
plausible axiom text are not owner execution/proof receipts and cannot mint
`ModelProven`.

## Stop conditions

- At most three fix/verify cycles.
- Do not rerun an unchanged green gate.
- Never infer `SourceRefined`, live authority, crash durability, semantic
  equivalence, native correctness, performance, or RSS from model/replay data.
- Preserve the torn-final-newline quarantine counterexample.
- Keep `generation_manifest` unsupported in this journal until its owner
  explicitly changes the production protocol and the model is re-reviewed.
