# Remaining memory execution routes — bounded read-only audit

Worktree: /private/tmp/simple-release100-reconciled-20261106. No source edits or runtime executions. Repair count remains4. Targeted cycle4 static review found the classifier-before-bounds issue addressed; this audit does not repeat that review or qualify any runtime.

## Core AST / inprocess probe

Actual chain: src/app/test_runner_new/inprocess_probe.spl:28 calls core_interpret after setting SIMPLE_NO_JIT=1. src/compiler/10.frontend/core/interpreter/mod.spl:167 _core_run_pipeline resets evaluator/AST, parses with core_frontend_parse_reset, resolves locals, checks capture writes, then calls eval_module at194. Neither typed ownership admission nor the new HIR CFG adapter is called there. All full-module public variants share that pipeline; core_interpret_expr is a separate expression-only API.

Dependency boundary matters: core/interpreter/module_loader_core.spl:501 load_module recursively discovers imports, accepts already-loaded/lazy aliases, then at615 calls eval_decl for dependency global/enum/impl/CLI initializers. A check only in inprocess_probe or immediately before each initializer cannot prove no earlier entry/dependency side effect occurred. The complete closure must be admitted before the first evaluation and must remain bound to the exact source generation later loaded. The lazy and already-loaded paths need the same generation authority.

Existing canonical conversion/admission owners:
- frontend/_FlatAstBridge/module_assembly.spl:295 flat_ast_to_module converts the core AST to ParserModule; it records typed nogc_strict at1288 from the parser-owned module marker. Do not add substring scans of @no_gc.
- frontend/frontend.spl:369 parse_full_frontend and scope/target-receipted variants own parser preprocessing/source semantics. The reference-only parse_and_build_module_checked_reference_v1 rejects conditional source and is therefore not a general replacement.
- driver_source_pipeline_loading.spl:213 load_sources_impl owns closure discovery; driver orchestration stage_parse and stage_lower_hir own canonical parsing/lowering; driver_hir_pipeline_lowering.spl:2589 lower_to_hir_impl and driver_hir_pipeline_support.spl:499 driver_admit_nogc_param_effects_v1 own typed effect/source admission.
- Existing ownership_provider_index_v1 and check_hir_ownership_with_live_providers_v1 provide the reusable checked-HIR closure validation. No target MIR or second ownership solver is needed.

Concrete next API proposal (new, not implemented): a driver-layer source-closure preflight owner, driver_core_ast_ownership_preflight_v1, returning a live generation-bound source snapshot set plus diagnostics. It invokes canonical source/parse/HIR stages without executing, then existing ownership checks. The top-level runner/composition wires this into a core evaluation admission interface; layer10 must not directly import layer80 and create a compiler dependency cycle. Core full-module entry and module-loader registration/initialization must require the live admitted source generation for strict modules, and evaluate the captured sources instead of rereading changed files. A missing adapter can refuse strict execution temporarily, but that is containment, not completed valid Core support. A naked checked Boolean or a path/name allowlist is insufficient. Do not call parse_and_build_module while the evaluator depends on the live global core AST arena unless the arena is captured/restored or preflight finishes before evaluator parsing begins.

Regression proposal: new core_ownership_entry_spec.spl alongside test/02_integration/compiler/core_interpreter_intensive_spec.spl, executed through an admitted compiled inprocess_probe. Cases: local move/reuse rejects; exclusive terminating arms succeed; legacy entry printing a marker imports invalid strict dependency and neither entry nor dependency initializer marker appears; lazy/alias dependency same result; dependency source mutation after admission invalidates generation. Existing intensive spec has _can_run=false and prints SKIP, so it cannot supply positive execution evidence.

## Cached SMF

Actual chain: driver_api_interpret.spl:26 interpret_file tries try_load_smf_cached before source mode. Cache helper56 checks manifest version/ABI, artifact presence, live source/interface hash and validate_smf freshness, then sets CompileMode.SmfExec at107. watcher/smf_manifest.spl:24 SmfManifestEntry has source/cache/ABI/interface/config fields but no ownership checked-producer or dependency-closure proof. Its gate154 admits version+ABI only. Source freshness is not evidence that ownership checking ran on the emitted artifact.

driver_orchestration.spl:420 dispatches execute_smf; driver_pipeline_execution.spl:41 sends path directly to static_jit_lane.spl:61. The Cranelift lane adapter static_backend_cranelift_jit_lane.spl:43 calls CodegenPipeline.load_smf_and_execute. codegen.spl:712 loads JitInstantiator metadata, requests main, and returns the resolved address as an integer at731; this inspected body does not itself call that address. Thus successful end-to-end execution is NOT established by this source trace. Builds without a linked JIT lane already refuse SMF execution; that does not close ownership requirements in capable compositions. Orchestration contains source/parse/HIR stages before final mode dispatch, but no inspected gate binds any HIR verdict to the exact executable SMF bytes; do not claim those stages certify the artifact.

Concrete next change: add an ownership-aware cache decision at try_load_smf_cached using canonical typed closure policy, never source spelling. If the closure is strict and the artifact lacks an admitted ownership proof, choose the full checked source interpreter path (or return a precise admission error for explicit source-less SMF execution). Valid strict source then remains usable, although cached artifact support remains OPEN. A full cache implementation must extend the canonical SMF producer/manifest/loader contract with checker-policy version, exact source/dependency generation identities, checked summaries, target/options and artifact digest bound at successful build publication. Consumer must verify that complete proof before metadata instantiation or executable mapping; setting gc_off or accepting an arbitrary serialized checked flag is not a proof. Explicit SmfExec and lower-level lane/loader entry must share this admission, not merely the convenience cache helper. Existing ABI/interface admission must remain intact.

Regression owners: existing driver/smf_manifest_gate_spec.spl, cache/smf_manifest_source_hash_verification_spec.spl and watcher/smf_manifest_load_positive_control_spec.spl. Add source-matched but ownership-unchecked strict artifact refusal/fallback; matching current producer positive execution in a real capable composition; changed dependency/body/target/policy/artifact digest negatives; legacy cache compatibility; absent JIT lane explicit unsupported (not PASS). Assert entry/initializer markers absent on failed admission. An old source-hash spec documents a zero hash stub outside interpreter, so do not infer live artifact freshness from its negative-only cases.

## Recommended sequence

1. Extract one reusable no-execution source-closure/HIR preflight from existing driver owners and bind its captured source generation; consume it from the Core composition and cache decision.
2. Implement genuine Core valid/invalid compiled entry tests including dependency effects and lazy/alias paths.
3. Contain unchecked strict cached artifacts via checked-source fallback, while keeping full artifact proof semantics OPEN.
4. Implement producer-to-loader artifact proof and demonstrate real cached positive execution; investigate address-return behavior separately before claiming execution parity.

No core route, SMF route, full44AC/12FV obligation or release verification is marked complete by this investigation.

## Shared immutable source-provider dependency

The immutable closure source provider is owned by the parallel source-overlay
lane (debug_truth). Reuse its captured bytes, canonical resolver membership and
generation identity for Core preflight/evaluation; do not introduce a second
source-provider implementation. Its concrete API is still under implementation.
The Core adapter requires snapshot reads for lazy materialization and an explicit
check that already-loaded modules belong to the admitted generation. Diagnostic
retention belongs to the separate compiler diagnostic lane. This report makes no
claim that every streaming/cache read seam has been audited.
