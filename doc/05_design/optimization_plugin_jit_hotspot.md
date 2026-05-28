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

Backend policy lets Simple keep SSA/escape/borrow-informed pre-optimization for
Cranelift or interpreter JIT planning while skipping redundant Simple-side
canonicalization under LLVM when the LLVM pipeline will run equivalent
mem2reg/SROA scalar promotion.

`src/compiler/60.mir_opt/mir_opt/var_reassign_analysis.spl`:

- Add `VarReassignAnalysis`.
- Add `SsaVarTransformResult`.
- Add `analyze_var_reassign_blocks`.
- Add `var_reassign_analysis_to_jit_facts`.
- Add `ssa_var_transform_blocks`.

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

`test/compiler/mir_opt/var_reassign_analysis_spec.spl` adds MIR analyzer coverage:

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
