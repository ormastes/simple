# Generic formal verification hardening plan

<!-- codex-architecture -->
Date: 2026-10-18. Status: implementation and qualification plan; production refinement NOT PROVEN.
Destination: `doc/03_plan/generic_formal_verification_hardening_plan.md` on `release_phase3`.

## 1. Scope and current authority

This plan preserves the original seven monomorphization criteria and the selected full C1–C7 formal scope.
It extends their acceptance evidence; it does not redefine a reduced model as compiler correctness.
The source baseline inspected is `origin/release_phase3` at `e6a4904a9faf67c4ee11d199cb197b002a9bf21c`.
The composed donor tree is `simple-utf8-external-text-root-20261018`; dirty-file pins, not its HEAD, identify its changes.
The documentation branch is `work/generic-formal-hardening-plan-20261018`; landing is a separate root-owned operation.

| Evidence at drafting | What it establishes | What remains open |
|---|---|---|
| Lean 4.30.0 retained eight-target type-inference project PASS | Exact repaired model project builds and canonical harness succeeds | Production compiler refinement, actual generator and native behavior |
| Earlier lazy-index and six-default-target replay PASS | Those pinned models, separately recorded | Do not sum overlapping project/model counts |
| Typed declarations, nominal bodies and mixed scalar source review GO | Reviewed donor implementation and API oracles | Absent from inspected release branch; 36 nominal-body API scenarios UNRUN |
| Hand-authored nominal/scalar Lean fixtures PASS | Reference target syntax and selected definitional computations | Actual generated output and source-to-proof correspondence |
| Generic structural/owner/Throws repairs in donor | Source-reviewed prerequisite work | Release files differ; exact composition and execution still required |
| Existing formal receipts, validators and replay interfaces | Typed infrastructure and bounded checks exist | Canonical fresh/independent replay authority still refuses admission |

The eight-target receipt is `proof-constraint-models-root-20261018/verification-cycle1/results.json`, SHA-256 `9c1c72c06c4d1d0ca7d01bb02ae1790e85a4b1f60d5d9800009d480c8a58a7ae`.
Its stages are ContractsConstraints, TypeInferenceCompileConstraints and canonical-eight-target-project, all exit 0.
The earlier nondefault constraint failures remain historical receipts; the repaired proof branch is `efa45d41a8901f338e7a450f2e8cdfb49732907f`, not established landed here.
Retain source, tool, artifact, stdout/stderr, trust-scan and complete/quiescent watchdog pins beside every result.
Native/interpreter/platform qualification for the complete composed feature remains UNRUN or blocked; no overall PASS follows from this document.

## 2. Original seven generic gates

Source contract: `doc/03_plan/compiler/generics/native_monomorphization_plan_2026-07-17.md`.
Historical command examples are not authorization to restore seed execution; use the current qualified pure-Simple route.

| Gate | Production owner | Required actual-API and semantic oracle |
|---|---|---|
| G1: retain typed HirFunction templates | `src/compiler/40.mono/monomorphize/table.spl` and `monomorphize_integration.spl` | Retained and archived bodies preserve symbol, signature, metadata and source identity; no Any erasure |
| G2: recursive substitution | `src/compiler/40.mono/monomorphize/type_subst.spl` | Signature/body/effects/Throws/owners and every current type-bearing node substitute consistently |
| G3: collect and deduplicate | `src/compiler/40.mono/monomorphize_integration.spl` | Explicit/default/inferred arguments and secondary roots reach one fixed point without cross-owner collisions |
| G4: insert specialized clones | `src/compiler/40.mono/monomorphize/engine.spl` plus integration | Actual inserted body/signature/symbol differs appropriately; declaration presence alone is insufficient |
| G5: rewrite calls | `src/compiler/40.mono/monomorphize/rewriter.spl` plus active integration path | Rewritten target, return type, effects and owner agree with the inserted specialization |
| G6: templates do not emit | Active integration and backend module emission | Unreached templates excluded; reached unsupported cases fail before MIR/native publication |
| G7: fail-closed post-mono boundary | `src/compiler/40.mono/verify/post_mono_verify.spl` and driver | No unresolved types/owners, stale signatures or incomplete specialization can pass publication |

These gates are not seven independent proofs or a completion percentage.
The broader M1–M9 obligations remain: non-type arguments/bounds, complete traversal/roots, layout/drop/witness/vtables, engine parity and bounded caches.
First confirmed new defect: `MonoTemplateSignatureV1` in `src/compiler/40.mono/mono_archive_types_v1.spl` omits declaration effects.
The active integration builds caller signatures with empty effects; effect-only archive drift is consequently absent from its signature digest.
Other archive pins may still reject drift; an end-to-end replay or security bypass is not established by the digest omission alone.
Prioritize a reviewed transport/substitution/digest repair with real retained/archive call and method-rewrite tests; its fix is pending, not claimed landed.
Do not patch unrelated baseline sites merely because they appear in a failed compiler log; establish ownership and causal evidence first.

## 3. Full formal scope and next closures

| Clause | Existing owner/evidence | Required hardening closure |
|---|---|---|
| C1 typed VIR | `src/compiler/50.mir/verification_ir.spl`, `verification_call_identity.spl` | Bind actual typed/woven compiler artifact, source spans, call identities and producer provenance to VIR |
| C2 data/semantic export | `src/plugins/backend_lean/lean_type_declarations.spl`, `lean_nominal_body.spl` in donor | Qualify generated declarations and supported bodies; add explicit recursive/union/aggregate-flow semantics in bounded slices |
| C3 contracts/obligations | `src/compiler/50.mir/verification_contract_bridge.spl`, `verification_obligation_closure.spl`, `verification_obligation_module.spl` | Generate non-vacuous complete dependency closure from the actual canonical module |
| C4 CFG/termination | `src/plugins/backend_lean/lean_mir_translate.spl` | Structured branches/loops, termination and invariants; reject unsupported graphs without dropping blocks |
| C5 memory/arrays | Same translator and `src/compiler/50.mir/verification_region_effects.spl` | Exact heap/ownership/frame, fixed-array/checked arithmetic and alias/cancellation semantics |
| C6 trust/replay | `src/compiler/90.tools/verify/checker.spl`, `replay_runner.spl`, `formal_gate_collectors.spl` | Provision trusted exact resolvers and fresh/independent kernel evidence; bind all roots and tool identities |
| C7 translation validation | `src/compiler/60.mir_opt/mir_opt/dce_translation_validation.spl`, `result_abi_translation_validation.spl` | Validate real before/after compiler artifacts; demonstrate deliberate corruption is rejected |

C2 donor coverage is acyclic struct/enum declarations, exact signatures and pure single-entry-block construction/projection.
Mixed scalar support reuses admitted modular arithmetic, bitwise/equality and unary semantics with exact MIR type/liveness checks.
General calls, mutation, enum elimination, recursive graphs, unions and arbitrary CFG are not implicitly admitted by those source bridges.
Signedness-sensitive division/order/shifts, unchecked layout guesses and unsupported IEEE behavior must retain precise refusals.

## 4. Common contracts and private implementation owners

`src/compiler/00.common/assurance/` owns shared evidence schemas; reuse `formal_interfaces.spl`, `formal_receipt.spl`, `formal_status.spl`, `replay_receipt.spl` and `proof_dag.spl`.
Use existing `ProofObligationV1`, `CompilerCertificateV1`, `ProofReceiptV1`, `VerificationCacheKeyV1` and typed evidence classes.
`CompilerCertificateV1.independently_checked` or a self-consistent certificate hash is not an external trust authority.
The common contract must consume a resolver-bound checked receipt; caller booleans, filenames or adjacent editable manifests cannot grant acceptance.
If an engine interface is needed, define the stable typed trait at this common boundary and implement adapters beside existing `ProofChecker`/replay owners.
The interface takes immutable obligation/artifact/tool-policy identities and returns typed checked, rejected, unknown, timed-out or tool-failure results.
It must not return an unstructured success string, mutate compiler state, or promote evidence class on behalf of the caller.
Keep parser grammar in frontend, substitution in mono, VIR lowering in MIR, backend mapping in backend and replay process control in verify.
Loader/interpreter consume common admission contracts; they do not call sibling-private backend or proof-checker internals.
Share stable format/tree nodes upward when necessary; avoid a second serializer, grammar, test harness or ad hoc proof cache.

## 5. Source-to-proof linkage and certificate admission

1. Freeze the actual source closure, dependencies, compiler/runtime, target and resolved policy; retain the canonical collector output.
2. Parse/name/type/effect-check, expand and weave through real owners; bind original/expanded spans and ordered join-point decisions.
3. Capture the exact specialized typed artifact at the production pass boundary, with schema/version and reachable owner map.
4. Translate only the declared semantic subset to VIR; a missing node/type/effect/call/layout translation is an error with source location.
5. Derive obligations and their proposition hashes internally from that artifact, including preconditions and non-vacuity witnesses.
6. Bind each compiler transformation edge to before/after semantic hashes, pass/version, refinement relation and checker receipt.
7. Generate the actual Lean module, execute the existing checker, enumerate theorem roots and audit their transitive axioms.
8. Replay the same module/root/artifact through the required evidence class; a reference model or different root cannot substitute.
9. Reduce all reachable dependencies to the existing final trust-closure obligation; publish atomically only when every required edge closes.
10. Bind admitted evidence to the exact executable/package and loader generation; changed artifacts revoke or invalidate acceptance.

Compiler/body/model encodings require a documented relation, not merely equal filenames, matching tokens or separately passing examples.
Universal refinement, per-artifact translation validation, approved external TCB and monitored assumptions remain distinct evidence classes.
Class/trait generic calls additionally bind implementation selection, witness/vtable/drop/layout identity and required bounds to the call contract.
Reject missing or ambiguous implementation/witness evidence; never replace a bound proof with an unconstrained type or erased effect.

## 6. Identity, profiles, configuration and invalidation

Active structural identity belongs to `src/compiler/40.mono/nominal_type_identity.spl`; archive transport belongs to `mono_archive_types_v1.spl` and integration.
`src/compiler/40.mono/monomorphize/mono_key.spl` already separates semantic and artifact keys; prove the active cache path actually consumes the required identity.
Semantic identity includes definition owner/body/schema, recursive type arguments, array lengths, tensor dimensions/device, effects/Throws, const/capability arguments and bounds/witnesses.
Do not use raw SymbolId alone across providers, raw encoded HIR as a substitute for canonical meaning, or hash equality without collision-safe comparison.
Artifact identity adds compiler/pass/toolchain, target/data layout/pointer width/CPU features, backend/ABI, resolved assurance policy and complete reachable dependency closure.
Bind collection policy, budget, profile byte digest/workload/target slice, tag representation and comparator/hash/equality contracts where they change semantics or layout.
Existing routing owners: `src/app/cli/collection_planner_options.spl`, `src/app/io/_CliCompile/native_collection_profile.spl`, `src/compiler/80.driver/driver_collection_planner.spl`.
Existing artifact reuse owners: `src/app/cli/native_build_warm_receipt.spl` and `src/compiler/80.driver/cache/compile_options_hash.spl`.
Dynload identity includes source/GTPL schema, callable body, ABI, provider closure, load generation and actual backend publication authority.
Use `src/compiler/99.loader/completeness_seal/source_manifest.spl`, `provider_call_boundary_v1.spl` and `module_loader_compat.spl` at their real boundaries.
Aspect identity includes ordered advice/weave plan, join points, completeness/facet generation and leases; reuse `aspect_lifecycle_gate.spl` and common composition receipts.
Invalidate on any relevant change, including effect-only drift, profile/tag/ABI/backend changes, provider replacement and weave-order changes.
Test same-input cold/warm equivalence, each single-field mutation, collisions, stale archives and interrupted writes; never force cache hits or rewrite foreign bindings.

## 7. Memory, lifetime and performance

`src/compiler/40.mono/monomorphize/cache.spl` owns bounded retained/disk cache accounting; active integration caches need their own measured ownership audit.
Check loaded-entry count/LRU reconstruction, replacement accounting, zero/full capacity, eviction and malformed persisted entries through actual cache APIs.
Track specialization count, reachable roots, body bytes, generated code size, live cache bytes, cold/warm time and peak RSS on representative generic projects.
Select numerical budgets from recorded baselines before acceptance; an unmeasured target or skipped efficiency spec cannot establish performance.
Bound recursion/queue growth and report cycles or resource exhaustion explicitly; deduplicate semantically equivalent requests without discarding distinct configurations.
Proof-cache entries own immutable dependencies and artifact lifetimes; eviction must not invalidate an active checked receipt or expose a reclaimed handle.
Dynamic unload/reload must preserve lease/refcount/generation checks, terminal idempotence, rollback and no-ABA behavior across asynchronous completion.
Exercise use-after-move, stale callable/witness, failed publication, cancellation and reclaim/reuse with deterministic scheduling or public APIs, not sleeps or invented observations.
Use existing resource watchdogs and process/environment facades; no new global cache registry or unbounded worker fanout for verification.

## 8. Trust and failure policy

Existing owners: `src/compiler/00.common/assurance/trust_audit.spl` and `src/compiler/90.tools/verify/replay_runner.spl`.
Every emitted theorem root needs kernel acceptance plus a transitive axiom report; scan source and compiled-root evidence together.
Reject `sorry`, `admit`, `sorryAx`, `Lean.trustCompiler` and undeclared project axioms; do not silently expand the approved foundational TCB.
Minimal-mode axiom declarations cannot count as proof of function behavior or satisfy a verified-profile release gate.
Solver `unknown`, timeout, unsupported construct, malformed output, missing root, tool failure and incomplete dependency closure are non-success states.
SMT/SAT/model-checker evidence needs the selected independently checked certificate or explicitly approved TCB class, not an exit code alone.
Fresh Lean replay and independent-kernel replay are different classes; missing authority stays unavailable even when a local model build succeeds.
Bind exact Lean/Lake/library/solver/tactic/trust-policy versions and bytes; policy or tool changes invalidate affected cached evidence.
Preserve failed attempts and diagnostics. No seed/interpreter fallback, fake callable, stub proof, ignored diagnostic or automatic retry may manufacture a PASS.

## 9. Modern SSpec and negative controls

Use `doc/05_design/infra/sspec/modern_sspec_typed_evidence_design.md` and existing `src/lib/common/spec/evidence/` contracts.
Use the existing runner, `std.spec`, `std.spec.step`, typed selectors/oracles/manifests and docgen; do not create a new test toolchain.
Executable specs stay under `test/`; `doc/06_spec/` contains generated Markdown/evidence only, never executable `_spec.spl` files.
Assertions must consume actual parser/HIR/mono/archive/MIR/backend APIs and compare semantic artifacts, returned bodies/signatures or exact diagnostics.
For each claim, retain source/input/tool hashes, selected subset, command, artifact hash, outcome, elapsed/RSS and requirement-to-oracle mapping.
Use existing generic owner/default/effect/transport/post-mono specs, `test/01_unit/compiler/mono/mono_key_spec.spl` and `mono_cache_efficiency_spec.spl`.
Use `test/01_unit/compiler/mir/verification_ir_spec.spl`, verification trust/replay specs and `test/03_system/compiler/formal_verification_2_0_spec.spl`.
Extend the existing `lean_type_declarations*_spec.spl` and `lean_nominal_body_spec.spl`/`compiler_lean_nominal_body_spec.spl` owners for actual generated-module acceptance.
Negative controls must alter owner, effect/Throws type, array size, tensor/device, bound witness, schema, profile/tag/backend/ABI, generation and weave order independently.
Also corrupt generated Lean, theorem root, compiler certificate edge, emitted body and tool hash; each must fail at its owning boundary without publication.
Prove the runner executes a deliberately failing body; skipped tests, placeholder success, scanner self-tests and name-only inventories do not qualify semantic behavior.
Hand-authored reference targets remain REFERENCE_TARGET_ONLY; finite model agreement remains model evidence until related to actual production output.
Run each acceptance criterion once on its exact inputs; invalidate only checks affected by changed evidence, and stop after three review/fix cycles per feature.

## 10. Phases, owners and exit gates

| Phase | Owner | Exit gate |
|---|---|---|
| P0 baseline/bug closure | Root merge owner + generic implementation reviewer | Exact release/donor deltas, source-pinned effect-carrier fix, reviewed tests and immutable historical receipts |
| P1 generic semantics | Mono/HIR owners | G1–G7 real API gates; retained/archive/default/inference/bounds/layout/owner tests; no unresolved publication |
| P2 admitted formal subset | MIR/VIR and Lean backend owners | Actual generated modules accepted; negative semantic controls reject; C1–C5 coverage ledger names every unsupported construct |
| P3 proof authority | Common assurance + verify/replay owners | Trusted resolver, complete obligation DAG, root/axiom audit and required fresh/independent replay receipts |
| P4 dynamic/profile closure | Loader/aspect/collection owners | Real callable publication, lifecycle/reload and every identity mutation invalidates correctly |
| P5 resource/engine qualification | Root-qualified runner/backend owners | Native/interpreter/backend/platform matrix, cold/warm/cache/lifetime/code-size budgets and core/lib/MCP smoke evidence |
| P6 landing/release | Root, independent final reviewer | Reviewed exact diff, green required checks, docs/manifests current, PR lands; promotion uses the same admitted artifacts |

Parallel sidecars: N/A for this drafting task; independent generic bug work is a separate source packet and cannot alter this plan's evidence status.
Plan final reviewer: `astra_warning_fix_review`; merge/landing owner: root.
Each implementation phase assigns a primary owner and independent normal/highest-capability reviewer before changing shared files.
The root serializes composition and landing, preserving unrelated work; a docs-only merge does not certify or release unlanded source packets.
Acceptance requires an explicit matrix per clause: source-coded, source-reviewed, executed, kernel-replayed, artifact-linked, platform-qualified and landed.
No aggregate percentage, model count or successful bootstrap replaces a missing semantic gate.

## 11. Source references and evidence retention

- Original seven: `doc/03_plan/compiler/generics/native_monomorphization_plan_2026-07-17.md`.
- Full formal contract: `doc/04_architecture/simple_formal_verification_2_0.md` and `doc/05_design/simple_formal_verification_2_0.md`.
- Selected-scope reconciliation: retained `latest-robust-plan-matrix-20261018/` and `07_formal-full-scope-matrix.md`; stale C2 absence rows are superseded only by reviewed donor source.
- Model receipts: retained `generic-formal-replay-20261018/` and `proof-constraint-models-root-20261018/verification-cycle1/`; no reruns required for unchanged green inputs.
- Reviewed unlanded bridges: retained `lean-type-declarations-20261018/revision2/`, `lean-nominal-body-20261018/revision2/` and `lean-nominal-scalar-body-20261018/`.
- At landing, root attaches portable receipt/manifests or stable artifact links and records the actual merge commit; developer-local paths alone are not release authority.
