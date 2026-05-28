<!-- codex-design -->
# Optimization Plugin JIT Hotspot Detail Design

## Source Changes

`src/compiler/60.mir_opt/mir_opt/pattern/rule_engine.spl`:

- Add `OptimizerProviderKind.JitHotspot`.
- Add `optimization_rule_provider_is_runtime_hotspot`.
- Add `optimization_rule_provider_builtin_jit_hotspot`.
- Add backend applicability metadata with `OptimizerBackendKind`,
  `OptimizationBackendPolicy`, default all-backend behavior, Cranelift/LLVM
  name parsing, and provider helpers to apply or skip a provider for a backend.

The helper constructs a built-in, hot, pipeline-pass provider so runtime hotspot providers do not accidentally use dynamic lookup or per-site table construction.

`src/compiler/60.mir_opt/optimizer_manifest.spl`:

- Add `backend_policy` to manifest pass entries and propagate it into dynamic
  pass provider descriptors.
- Add `manifest_pass_entry_new` so existing dynamic manifest construction gets
  an explicit all-backend default without positional-field drift.
- Add `manifest_pass_entry_with_backend_policy` and
  `manifest_pass_entry_new_with_backend_policy` so manifest construction can
  declare backend-specific apply/skip policy directly.
- Add `dynamic_pass_registry_for_backend`,
  `dynamic_pass_registry_names_for_backend`, and
  `dynamic_pass_registry_skipped_names_for_backend` so backend planners consume
  a pre-filtered plugin view instead of duplicating policy checks.
- Add `run_manifest_pattern_rules_for_backend` so manifest-provided pattern
  rewrites execute only when at least one registered pass from that manifest is
  applicable to the requested backend. Rules-only manifests remain
  backend-neutral because they have no pass-policy anchor.

Backend policy lets Simple keep SSA/escape/borrow-informed pre-optimization for
Cranelift or interpreter JIT planning while skipping redundant Simple-side
canonicalization under LLVM when the LLVM pipeline will run equivalent
mem2reg/SROA scalar promotion.

`src/compiler/60.mir_opt/mir_opt/mod.spl`:

- Add `optimizationpipeline_for_backend`.
- Add `optimizationpipeline_passes_for_backend`.
- Add `mir_pass_applies_to_backend`.
- Mark low-level scalar cleanup passes that LLVM already owns
  (`common_subexpr_elim`, `global_value_numbering`, `loop_unroll`, and
  `strength_reduction`) with skip-LLVM provider policy.

The canonical pipeline remains the source of pass ordering, but backend-aware
callers now consume a filtered view. Cranelift and the accepted `cranlift` alias
retain Simple-side scalar cleanup because Cranelift benefits from cleaner MIR
before lowering. LLVM keeps high-level Simple-owned proofs such as bounds,
target narrowing, pattern idioms, and byte/copy cleanup, but skips duplicated
scalar/loop cleanup so the LLVM default pipeline can handle it once IR has been
lowered.

`src/compiler/70.backend/backend/backend_helpers.spl`:

- Convert the backend helper optimization level to MIR `OptLevel`.
- Resolve the effective backend name before direct codegen.
- Run `optimize_module_for_backend` before LLVM, LLVM-lib, Cranelift, and
  generic backend codegen.

This closes the direct-backend gap where driver compilation could bypass the
canonical MIR optimizer entirely.

`src/compiler/60.mir_opt/mir_opt/var_reassign_analysis.spl`:

- Add `VarReassignAnalysis`.
- Add `SsaVarTransformResult`.
- Add `SsaPhiPlan`.
- Add `SsaPhiMaterializeResult`.
- Add `SsaPhiLoweringKind`.
- Add `SsaPhiLoweringPolicy`.
- Add `analyze_var_reassign_blocks`.
- Add `var_reassign_analysis_to_jit_facts`.
- Add `ssa_var_transform_blocks`.
- Add `ssa_phi_plans_for_blocks`.
- Add `ssa_materialize_phi_plans_for_blocks`.
- Add `ssa_phi_lowering_policy_for_backend`.
- Add `ssa_phi_backend_can_lower`.

The analyzer treats repeated definitions of the same MIR `LocalId` as `var`
reassignment candidates. It is conservative: a reassigned local is not eligible
for SSA-var hotspot planning if it is written after an outstanding borrow or if
the reassigned local escapes through return, call/intrinsic arguments, stores,
or field writes. Analyzer output feeds `JitVarOptimizationFacts`, so the JIT
planner can consume compiler-derived facts instead of hand-authored booleans.

The initial SSA transform is intentionally limited to straight-line single-block
MIR. It renames repeated definitions to fresh `LocalId` values and rewrites
subsequent operands in the block to the latest version. Multi-block CFGs and
branching terminators return `requires phi nodes` until phi insertion exists.
For simple diamond-shaped `if`/`else` CFGs where both arms assign the same
local before jumping to a shared join block, the rejection now includes
`phi_required_count` and `phi_required_locals` in `SsaVarTransformResult`.
`ssa_phi_plans_for_blocks` turns that same shape into concrete plan records:
join block ID, original local ID, planned then/else value locals, and the
planned phi destination local.
`ssa_materialize_phi_plans_for_blocks` rewrites the branch definitions to those
fresh value locals, inserts `Intrinsic(Some(phi_dest), "__simple_ssa_phi", ...)`
at the join, and rewrites join-block uses to the phi destination. This avoids a
new MIR opcode until backend-native phi lowering is implemented.
`ssa_phi_lowering_policy_for_backend` makes the backend contract explicit:
Cranelift and the accepted `cranlift` alias lower pseudo-phis to block
parameters, LLVM lowers them to native phi nodes, the interpreter keeps the
fallback intrinsic, and unsupported backends must reject pseudo-phi MIR instead
of compiling it with ambiguous semantics.

`src/compiler/95.interp/mir_interpreter.spl`:

- Add interpreter fallback handling for `__simple_ssa_phi`.

The interpreter uses the first incoming pseudo-phi operand as a deterministic
linear fallback. CFG-aware native backends should lower the pseudo-phi to
backend phi/block-parameter semantics; the interpreter fallback keeps
materialized optimizer MIR executable for tests and non-native paths.

`src/compiler/95.interp/execution/tiered_jit.spl`:

- Add `JitHotspotPlan`.
- Add `JitVarOptimizationFacts`.
- Add `JitHotspotRebuildPlan`.
- Add `jit_hotspot_profile_facts`.
- Add `jit_hotspot_plan_from_profile`.
- Add `jit_hotspot_plan_with_var_facts`.
- Add `jit_var_optimization_facts`.
- Add `jit_var_optimization_fact_list`.
- Add `jit_var_optimization_reason`.
- Add `jit_hotspot_rebuild_plan`.
- Add `jit_hotspot_rebuild_backend_name`.
- Add `jit_hotspot_plan_invalidate`.
- Add `jit_hotspot_consume_plan`.
- Add `JitHotspotSpecializationProvider`.
- Add `jit_hotspot_specialization_provider`.
- Add `jit_hotspot_consume_plan_with_provider`.
- Add `TieredJitManager.get_hotspot_plan`.
- Add `TieredJitManager.register_function_with_hotspot_facts`.
- Add `TieredJitManager.register_function_with_hotspot_specialization`.

The plan helper maps tiered JIT call counts to `profile.hot_count`, preserves `typed_mir` and `safe_deopt` as explicit guard facts, and reports why a plan is not eligible. This is intentionally pure Simple logic so unit tests do not need native JIT handles.

The compile-decision consumer runs before tier-1 native compilation. It accepts eligible plans, keeps the original source as the fallback compile input, and leaves Rust JIT execution APIs untouched. A specialization provider may replace the compile source only when it carries a non-empty specialized source and declares a semantic proof.

Var reassignment hotspot planning is intentionally fact-gated. Reassigned
`var` storage may enter a hotspot plan only when the planner has:

- `ssa.var_transform` for reassignment-to-SSA conversion.
- `escape.analyzed` and `escape.no_escape` so stack/local assumptions are not
  made for escaping storage.
- `borrow.reassign_safe` so reassignment does not invalidate an outstanding
  borrow.

Hotspot rebuild planning supports both Cranelift and LLVM at the policy layer.
Cranelift/`cranlift` rebuilds are tier-1, medium-cost plans. LLVM rebuilds are
tier-2, high-cost plans and remain ineligible until the tier-2 hot-count
threshold is reached and the LLVM backend is available.

`src/compiler/60.mir_opt/general_patterns.spl`:

- Add `BackendOptimizationRecommendation`.
- Add `all_backend_optimization_recommendations`.
- Add `backend_optimization_recommendations_for`.
- Add `backend_optimization_recommendation_names`.
- Add `backend_optimization_has_recommendation`.

The general pattern catalog now turns researched optimization items into
backend-aware plugin recommendations. Cranelift/`cranlift` keeps Simple-side
`ssa-var-canon` because var reassignment facts, escape facts, and borrow safety
are available in MIR before Cranelift lowering. LLVM skips `ssa-var-canon` and
selects `llvm-default-pipeline` because LLVM's backend pipeline can run scalar
promotion and cleanup itself. High-level MIR optimizations whose proofs are
frontend-owned, including bounds-check elimination, delimiter byte scans, and
checksum reducers, remain recommended for both backends.

## Tests

`test/unit/compiler/mir_opt/cipher/pattern_engine_spec.spl` adds a provider-contract test:

- JIT hotspot provider kind is `JitHotspot`.
- Load mode is built-in.
- Lookup kind is pipeline pass.
- Runtime hotspot predicate is true.
- Missing `safe_deopt` rejects execution.
- Providing all required facts allows execution.
- Backend policies can skip LLVM while still applying to Cranelift, including
  the accepted `cranlift` spelling from the user request.
- Expensive hotspot rebuild providers can be restricted to one backend.

`test/compiler/mir_opt/optimizer_manifest_backend_policy_spec.spl` adds manifest coverage:

- Manifest-created passes default to all backends.
- Dynamic provider descriptors can be given backend skip policies after loading.
- Registered dynamic pass descriptors can be filtered for Cranelift/`cranlift`
  and LLVM, including skip-list visibility for passes intentionally not run on
  a backend.
- Manifest pattern rules are applied to real MIR for Cranelift/`cranlift` when
  the registered pass applies, and are skipped for LLVM when backend policy
  excludes that pass.

`test/unit/compiler/mir_opt/var_reassign_analysis_spec.spl` adds MIR analyzer coverage:

- Repeated local definitions become SSA-transformable when local and
  borrow-safe.
- Reassignment after an outstanding borrow is rejected.
- Reassigned locals that escape through return are rejected.
- Analyzer output feeds `jit_hotspot_plan_with_var_facts`.
- Straight-line reassignment rewrites to a fresh SSA local and rewrites later
  operands to that version.
- Multi-block reassignment is rejected with `requires phi nodes`.
- Simple branch-merge reassignment reports the affected local IDs that need phi
  construction.
- Simple branch-merge reassignment produces a concrete `SsaPhiPlan`.
- Simple branch-merge reassignment materializes branch-local values and a
  `__simple_ssa_phi` pseudo-intrinsic in the join block.
- Backend lowering policy maps Cranelift/`cranlift`, LLVM, interpreter, and
  unsupported backends to explicit pseudo-phi decisions.

`test/unit/compiler/interpreter/mir_ssa_phi_intrinsic_spec.spl` adds interpreter coverage:

- `__simple_ssa_phi` stores the first incoming value into the destination as a
  deterministic linear fallback.

`test/unit/compiler/mir_opt/general_patterns_backend_recommendation_spec.spl` adds recommendation coverage:

- Cranelift/`cranlift` receives `ssa-var-canon` and general high-level MIR
  optimizations.
- LLVM skips `ssa-var-canon` and receives the backend-managed
  `llvm-default-pipeline`.
- Bounds-check elimination, byte-scan recognition, and checksum reduction stay
  recommended for both Cranelift and LLVM.

`test/unit/compiler/mir_opt/pass_descriptor_spec.spl` adds backend pipeline coverage:

- Cranelift/`cranlift` keeps low-level scalar cleanup passes.
- LLVM skips scalar cleanup passes duplicated by its backend pipeline while
  keeping high-level MIR passes.
- `llvm-lib` follows the same backend policy as LLVM.

`test/unit/compiler/interpreter/tiered_jit_hotspot_spec.spl` adds plan coverage:

- Cold profiles do not emit `profile.hot_count`.
- Hot typed profiles with safe deopt emit all required facts.
- Eligible plans require all runtime facts.
- Missing `safe_deopt` rejects planning without dropping hot-count facts.
- Var reassignment emits `var.reassignment`, `ssa.var_transform`,
  `escape.no_escape`, and `borrow.reassign_safe` facts only when supplied by
  analysis.
- Reassigned-var hotspot plans reject missing SSA transform, escaping storage,
  and unsafe borrow reassignment.
- Cranelift hotspot rebuilds are accepted at tier 1; LLVM rebuilds are deferred
  until tier 2 and marked high cost.
- Invalidation disables a previously eligible plan.
- Disabled providers do not consume plans and preserve fallback source.
- Eligible plans are consumed into compile decisions.
- Specialized source is selected only when semantic proof is present.
- Missing semantic proof preserves original-source compilation.

`test/perf/compiler/jit_hotspot_plan_bench.spl` adds benchmark coverage:

- Cold profile planning below the hot-count threshold.
- Ready profile planning with all runtime facts.
- Ready profile planning followed by explicit invalidation.
- Checksum-bearing CSV output for repeatable evidence reports.

## Documentation

Update:

- `doc/07_guide/compiler_optimization_plugin.md`
- `doc/04_architecture/simple_optimization_plugin.md`
- `doc/06_spec/app/compiler/feature/simple_optimization_plugin_spec.md`
- `doc/09_report/verify/optimization_plugin_jit_hotspot_perf_evidence_2026-05-24.md`

The docs distinguish compiler rewrites from JIT hotspot plans.
