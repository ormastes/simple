# Kernel + Pluggable Migration Plan

Status: ACTIVE IMPLEMENTATION; **NOT COMPLETE** (reconciled 2026-09-02).
Ordered so the bootstrap fixpoint
(`scripts/bootstrap/bootstrap-from-scratch.sh`, stage2/3 entry
`src/app/cli/bootstrap_main.spl` `:2085,2169,2212,2244`) stays green at every
phase. Phase 0-1 touch no kernel hot path. Every phase: an sspec that passes
AND fails under an injected bug (mutation-red), per
`.claude/memory` rule "SSpec dual check".
Architecture: `doc/04_architecture/compiler/plugin_arch/kernel_pluggable_partition.md`.
Design: `doc/05_design/compiler/plugin_arch/versioned_param_objects_and_interfaces.md`.

REQ-009/NFR-006 structural coverage is enforced by
`scripts/check/check-kernel-plugin-migration-evidence-matrix.shs`. It executes
one production-seam probe for every phase 0 through 8, then injects a defect
into that phase's implementation or selected-policy input and requires the
same probe to fail. Phase 7 additionally executes the non-native matrix row,
requires `BLOCKED` plus deployment denial, and verifies that the native
admission consumer binds candidate and Stage4 provenance digests. This does
not convert blocked SPipe, bootstrap, startup, or native rows to PASS.

Rust tooling update (2026-09-03): a generation-pinned authoritative session
now covers supervised rust-analyzer lifecycle, Cargo/Clippy structured
receipts, exact toolchain/build identity, cancellation, stale publication
rejection, and explicit incomplete results. Evidence is recorded in
`doc/09_report/kernel_plugin_authoritative_rust_ide_lint_session_2026-09-03.md`.

Documentation reconciliation (2026-09-02): final requirements are recorded in
`doc/02_requirements/feature/kernel_plugin_migration.md` and
`doc/02_requirements/nfr/kernel_plugin_migration.md`. The selected authority in
those final requirements and `kernel_closure.sdn` is
LLVM+Cranelift, ABI v1 now, `simple.sdn`, atomic APK-only coverage, and
baseline-relative RSS limits. For each architecture, maximum steady RSS is
`<=110%` of its admitted baseline and maximum growth across 20 requests is
`<=10%` of baseline RSS; a missing baseline fails closed. Structural
implementation is broad. At audited HEAD `1eb24a67d1c3`, compiler closure
passes with 1,979 classified files and zero forbidden edges, KPF performance
normal/mutation gates pass, and the native ABI matrix proves major rejection
and older-minor acceptance. This checkout still admits no runtime for the
focused SPipe command, the latest Stage3 attempt failed without a candidate,
and no cross-host bootstrap evidence exists.
Structural/checker results below are therefore kept distinct from runtime and
native qualification. The selected policy must be receipt-bound. Performance
qualification remains blocked until an admitted architecture-matched baseline
and qualifying measurement receipt exist.
REQ-KPF-008 worker-wire follow-up (2026-09-03): the canonical schema compiler
now generates a package-specific fixed worker-envelope projection containing
the schema digest, dense interface/operation slots, required-operation policy,
and overflow-safe frame bounds checks. Focused generator and generated-fixture
tests pass. The shared four-language malformed native-layout corpus now covers
truncated and oversized descriptors, reserved fields, overflow-safe offsets,
alignment failures, append-compatible tails, and a mutation guard. Broader
worker and product qualification remain separate gates.
The selected LLVM+Cranelift, ABI v1, `simple.sdn`, and atomic APK-only policy
set is structurally complete: defaults and admission bind those choices and
reject alternate policy inputs. Runtime/native rows remain blocked. The Stage3
recovery authority currently fails closed at
`stage2-transcript-environment-set-mismatch`, and the baseline authority
validator remains `WARN` pending one rerun of its corrected document-case
mutation plus real architecture-matched receipts.

## Authoritative implementation status

| Phase | Current determination | Authoritative source/test/report evidence |
|---|---|---|
| **0 — partition declaration** | **STRUCTURAL/CHECKER PASS; SPipe RUNTIME BLOCKED.** The fail-closed closure audit classified the owned compiler tree with zero unclassified, compiler-to-plugin, and K0/K1-to-P edges. | `doc/04_architecture/compiler/plugin_arch/kernel_closure.sdn`; `scripts/check/check-kernel-closure.shs`; `test/01_unit/compiler/plugin_arch/kernel_closure_spec.spl`; `build/review/final_phase0_phase5_audit.md` |
| **1 — ABI digest** | **EXECUTABLE PASS on admitted macOS arm64 runtime.** Typed-HIR field-ordinal digesting is compute-only and reached by both production HIR paths; field-sensitive/body-insensitive receipts passed. | `src/compiler/20.hir/abi_interface.spl`; `src/compiler/80.driver/driver_hir_pipeline_lowering.spl`; `test/01_unit/compiler/interface_compat/compile_interface_spec.spl`; `doc/09_report/compiler/kernel_plugin_migration_phase_1_2_4_executable_matrix_2026-09-03.md` |
| **2 — param objects and lint** | **EXECUTABLE PASS on admitted macOS arm64 runtime.** Append-only evolution, ordinal rejection, app-boundary environment decoding, typed parameters, and AST-backed linting passed. | `src/lib/common/plugin/aspect_params.spl`; `src/app/io/aspect_params_env.spl`; `test/01_unit/compiler/plugin_arch/param_object_lint_spec.spl`; `test/01_unit/compiler/aop/aspect_params_spec.spl`; `doc/09_report/compiler/kernel_plugin_migration_phase_1_2_4_executable_matrix_2026-09-03.md` |
| **3 — manifest identity** | **STRUCTURAL PASS; FOCUSED 6/0 EVIDENCE; STARTUP/NATIVE BLOCKED; `simple.sdn` SELECTED.** Production uses current schema 35 with legacy 34 rejection rather than the proposal's stale 4/3 literals. | `src/compiler/80.driver/watcher/smf_manifest.spl`; `src/compiler/00.common/assurance/package_pins.spl`; `test/01_unit/compiler/driver/smf_manifest_gate_spec.spl`; `build/test-artifacts/01_unit/compiler/driver/smf_manifest_gate/summary.txt`; `build/review/accepted_phase_0_4_m0_m4_phase8_verification_audit.md` |
| **4 — lint table seam** | **EXECUTABLE CORE PASS; FINAL REMOVE-ROW MUTATION RERUN PENDING.** Canonical per-rule identities are recomputed and shared negotiation returns `Ok` before dispatch. Added-row execution passed; stale test-cache reuse was fixed after the third permitted cycle. | `src/compiler/90.tools/lint/lint_rule_api.spl`; `src/compiler/90.tools/lint/static_rules.spl`; `test/01_unit/compiler/lint/lint_rule_table_spec.spl`; `doc/09_report/compiler/kernel_plugin_migration_phase_1_2_4_executable_matrix_2026-09-03.md` |
| **5 — backend port and P-static relocation** | **STRUCTURAL/CHECKER PASS; BOOTSTRAP/SPipe BLOCKED; LLVM+CRANELIFT SELECTED.** Non-K1 backends are relocated under `src/plugins/backend_*`; dispatch is policy-bound and table-routed through the selected combined composition. No admitted Stage2/3 receipt exists. | `src/compiler/70.backend/backend/backend_factory_full.spl`; `src/compiler/70.backend/backend/static_backend_registry.spl`; `src/compositions/kernel_llvm_cranelift/compiler/driver/bootstrap_k1_selected.spl`; `doc/04_architecture/compiler/plugin_arch/kernel_closure.sdn`; `scripts/check/check-phase5-backend-dispatch.shs`; `test/02_integration/bootstrap/plugin_edit_no_rebuild_spec.spl` |
| **6 — APK/SFFI negotiation** | **STRUCTURAL + NATIVE ABI MATRIX PASS; ORIGINAL SPipe/PRODUCT ADMISSION BLOCKED; ABI v1 SELECTED.** The native matrix admits matching-major and older-compatible-minor providers, rejects wrong-major and wrong-digest providers, performs one entry lookup, and rejects digest-check removal. | `src/lib/common/plugin/negotiation.spl`; `src/compiler/70.backend/backend/runtime_compiler.spl`; `test/01_unit/lib/sffi/dynamic_versioned_negotiate_spec.spl`; `test/02_integration/lib/sffi/native_dynamic_compatibility_matrix_test.shs`; `build/review/two_plan_completion_audit_current.md` |
| **7 — aspects as packs/kernel closure** | **STRUCTURAL PASS; ALL RUNTIME/NATIVE ROWS BLOCKED; ATOMIC APK-ONLY SELECTED.** Child-side APK activation, zero source rewriting, and produced-binary gates exist. Dual evidence is non-authoritative migration comparison only; no one-binary, dynload, parity, or startup row is qualified. RSS qualification requires an admitted per-architecture baseline, steady RSS `<=110%`, and 20-request growth `<=10%` of baseline RSS. | `src/lib/common/plugin/instrumentation_aspect_pack.spl`; `src/app/test_runner_new/test_runner_single.spl`; `scripts/check/check-kernel-phase7-matrix.shs`; `test/03_system/compiler/kernel_phase7_qualification_spec.spl`; `doc/06_spec/05_perf/compiler/plugin_arch/phase7_startup_and_parity_evidence.md` |
| **8 — package ranges** | **SOURCE CONTRACT PASS; EXECUTABLE RUNTIME BLOCKED; ORDERING BLOCKED BY PHASE 7.** Root CLI dispatch now calls compiled `lock`/`update` entrypoints rather than raw-source wrappers. Parsed fail-closed classification, deterministic range resolution, canonical `simple.sdn` location plus ABI-v1 receipt binding, and atomic lock/update writes are implemented. The source contract passed; the executable system rows cannot run because no admitted non-seed runtime exists, and Phase 7 is not qualified. | `src/app/pkg/requires_range.spl`; `src/app/lock/main.spl`; `src/app/update/main.spl`; `src/app/cli/_CliMain/main_and_help.spl`; `test/00_unit/scripts/kernel_plugin_phase8_source_contract_test.shs`; `test/03_system/app/pkg/feature/requires_range_spec.spl`; `doc/09_report/compiler/kernel_plugin_migration_phase8_completion_2026-09-03.md` |

The phase table below remains the acceptance contract. A structural `PASS` in
the status table does not replace its required SPipe, bootstrap, startup, or
native evidence.

| Phase | Scope (files) | Kernel hot path touched? | Acceptance | Proof (sspec) |
|---|---|---|---|---|
| **0. Declare the partition** | New `doc/04_architecture/compiler/plugin_arch/kernel_closure.sdn` listing K0/K1 directories/files (from partition §3); new `scripts/check/check-kernel-closure.shs` (fail-closed, `--selftest`) that FAILs if a K0 path imports a P path (`use` scan) or if a file under `src/compiler` is in neither list. Correct the stale "zero callers" text in `.claude/rules/commands.md` and `src/lib/scv/build_invalidation.spl:12,38,172`. | no | Verdict `PASS — n file(s) classified, 0 unclassified, 0 K0->P imports`; initial run may be RED (record baseline like `unbacked_extern_baseline.txt`). | `test/01_unit/compiler/plugin_arch/kernel_closure_spec.spl`: fixture tree with one K0 file importing a P file must FAIL; clean fixture PASS; empty fixture ERROR. |
| **1. Real ABI digest, compute-and-log** | `src/compiler/35.semantics/interface/compile_interface.spl` (+ `simple/abi-interface/v1` domain, field-ordinal encoder), `module_identity.spl:24-31` (`abi_interface_digest` real; others unchanged), new `src/lib/common/plugin/iface_id.spl` (`IfaceId`, `ParamHeader`, `ParamExt`). Digest is logged only; no build decision reads it (same posture as `module_identity.spl:3` today). | no (semantics layer, off the decision path) | Digest changes when a struct field is added/renamed/reordered; unchanged when a fn body changes. Existing `compile_interface_spec.spl` still green. | Extend `test/01_unit/compiler/interface_compat/compile_interface_spec.spl`: field-append changes abi digest but not compile-interface digest of callers; field-rename changes both; mutation: encoder dropping field type must be caught. |
| **2. Param-object convention + lint** | `PARAM-001..003`, `PLUG-001` in `src/compiler/90.tools/lint/` (P-static); `scripts/check/check-param-object-evolution.shs` (diffs `V<n>` vs `V<n+1>` ordinals between `main@origin` and tip). First adopters: `AspectParamsV1` (design §2.3) fed by the existing env vars at `driver_pipeline_aop.spl:68-80`; `McdcPolicy` already typed (`mcdc/dynamic_aspect.spl:128-163`). | weaver reads a record instead of env (one-time read at driver boundary; not per-node) | Env vars still work (front-end); `driver_pipeline_aop.spl` has zero `env_get`; lint FAILs a `V2` that reorders a `V1` field. | `test/01_unit/compiler/plugin_arch/param_object_lint_spec.spl` (each rule: clean PASS, dirty FAIL); `test/01_unit/compiler/aop/aspect_params_spec.spl` (env->record round-trip; presence bit set only when env set). |
| **3. Manifests carry identity, fail-closed** | `watcher/smf_manifest.spl` records `abi_digest`, `provides`, and `requires`; its checked reader immediately rejects every non-current schema. `simple.sdn` `provides:/requires:/link:` fields are parsed canonically by `package_pins.spl`; alternate manifest paths are rejected by Phase 8 admission. | manifest read at startup: one extra column compare, no hashing | A stale `.smf` with a mismatched `abi_digest` is rejected with a named code, not silently re-interpreted; legacy and unknown manifest versions fail during checked parsing. | `test/01_unit/compiler/driver/smf_manifest_gate_spec.spl`: legacy/unknown schema, wrong digest, malformed rows, and duplicate rows all reject; current matching identity admits. |
| **4. First P-static seam: lint rules as a table** | `90.tools/lint/_LintMain/lint_checks.spl:71,198,503,617,658` + sibling rule files -> `trait LintRule { fn iface; fn id; fn check(params: LintParamsV1, unit) }` and a static table; `src/app/lint/main.spl` unchanged. `simple.sdn` for `src/compiler/90.tools/lint` gains `provides: simple.lint.LintRule@1`. | no (lint is off the compile path) | Adding a rule = one new file + one table row; `check-kernel-closure.shs` proves no K0 file changed; bootstrap receipt for the lint unit shows `negotiate: Ok`. | `test/01_unit/compiler/lint/lint_rule_table_spec.spl`: a fixture rule registered via the table fires; removing it from the table silences it; a rule whose `iface.major` != host's is refused with `PLUG-E-MAJOR`. |
| **5. Backend port typed; non-bootstrap backends P-static** | `70.backend/backend_port.spl:15-25` -> `trait BackendPlugin` + `BackendPortV1` (design §4); `backend_factory_full.spl:113-137`, `codegen_factory.spl:37-41` dispatch via table; enum stays for cache ids (`compile_options_hash.spl:239,251`) but is derived from `BackendDescV1.name`. LLVM + Cranelift remain K1 (linked always); Wasm/Cuda/Hip/OpenCl/Vhdl/IrTc/Lean/Byl/Vulkan/LlvmLib/C become table entries under `src/plugins/backend_*/`. | one indirect call per compile (not per node) | Bootstrap with `--backend=llvm` and `--backend=cranelift` both green; `bootstrap_wide_inputs_hash` no longer includes `src/plugins/**`; editing a Wasm backend file does not change stage3's receipt hash. | `test/01_unit/compiler/backend/backend_port_negotiate_spec.spl`: each table entry negotiates Ok; a fixture plugin with `major: 2` is refused; `test/02_integration/bootstrap/plugin_edit_no_rebuild_spec.spl`: touch a P-static file, assert kernel object cache keys (`native_build_cache_scope_key`) unchanged. |
| **6. P-dyn negotiation on the APK gate and SFFI loader** | `aspect_pack.spl:2125-2205`: replace opt-in `required_core_*` (`:2196-2205`) by mandatory `negotiate(HostOfferV1, PluginAnswerV1)`; `sffi/dynamic_versioned.spl:170-187` reads `spl_plugin_entry_v1` via `spl_dlsym_checked` (`runtime_dynload.c:474`) and negotiates before returning a handle; `SIMPLE_ABI_VERSION` added to `runtime.h` and to `native_build_producer_identity` (`incremental.spl:250-252`). Remove `@unsafe(reason: "loads an unverified ...")` annotations only where negotiation now runs. | load path only (first facet use) | A pack/`.so` built against a different major is refused with `PLUG-E-MAJOR`; a pack built against an older accepted minor loads; `apk_try_facet` (resident) unchanged in cost. | `test/01_unit/lib/aspect_pack/negotiate_spec.spl` (reuse existing APK fixtures; mutation: skipping the digest compare must fail); `test/01_unit/lib/sffi/dynamic_versioned_negotiate_spec.spl`. |
| **7. Aspects as packs; bootstrap closure = kernel** | Coverage uses an APK `STARTUP` aspect carrying `AspectParamsV1`; bootstrap uses `APK_ACT_STATIC`, while tests use STARTUP/lazy facets. Production coverage is atomic APK-only; dual and source-rewrite paths are rejected. | weaver: none new; startup: table walk | A P edit preserves the kernel hash; a K0 edit changes it; coverage performs zero source rewriting; rejected dual input fails before execution; one-binary and dynload rows qualify separately. | `test/02_integration/bootstrap/inputs_hash_partition_spec.spl`, `test/02_integration/aop/coverage_aspect_pack_spec.spl`, and `test/03_system/compiler/kernel_phase7_qualification_spec.spl`. |
| **8. Package ranges (optional, after 7)** | Root `_CliMain` dispatches `update` and `lock` to their production entrypoints. `requires_range.spl` uses canonical caret/tilde satisfaction and binds ABI v1 plus `simple.sdn`; no backtracking solver is added. | no | `simple lock` writes deterministic `provides/requires` resolutions; unsatisfied ranges and rejected policy alternatives fail without replacing an admitted lock. | Unit, integration, and root-CLI system specs under `test/{01_unit,02_integration,03_system}/app/pkg*`. |

## Ordering rationale
- 0-1 are documentation + compute-and-log; bootstrap unaffected.
- 2-3 make the identity *recorded* before anything *depends* on it.
- 4 proves the pattern on a seam with no ABI surface and no hot path.
- 5 needs both K1 backends green before any backend moves out.
- 6 is the first change to a load path; it lands after the static path has
  exercised `negotiate` for two phases.
- 7 is the payoff: narrows the kernel rebuild trigger. It is last because it
  changes what the bootstrap script hashes.

## Non-goals
Patchpoints (`patchpoint_and_signing_prerequisites_2026-08-19.md:26-30`),
typed `facet<T>` (`typed_facet_witness_transaction_2026-08-26_tldr.md:3`),
`AspectRuntimeRegistry`, a shared `libsimple_runtime.so`, ECS in kernel/drivers
(`mdsoc_architecture_tobe.md:372-378`), a version-range solver.

## Selected user policy

- **1A:** LLVM-default plus explicit Cranelift K1.
- **2B:** ABI v1 now.
- **3A:** canonical `simple.sdn` manifests.
- **4A:** atomic APK-only coverage.
- **Performance authority (revised):** baseline-relative 10% policy. Maximum
  steady RSS is `<=110%` of the admitted native baseline; maximum growth across
  20 requests is `<=10%` of baseline RSS. Missing baseline fails closed.

The user selected this authority on 2026-09-02. The machine-readable authority is
`doc/04_architecture/compiler/plugin_arch/kernel_closure.sdn`; production
paths reject drift.
No performance row may pass without an admitted architecture-matched baseline
and a receipt proving both limits.

## Follow-on compile optimization

Persistent package/module indexing, TLDR+SMF metadata, one-package
invalidation, deterministic SCC scheduling, atomic publication, and removal of
hidden full-scan fallback are planned in
`doc/03_plan/compiler/perf/persistent_package_module_index_compile_optimization_plan_2026-09-02.md`.
