<!-- codex-design -->
# Optimization Plugin JIT Hotspot Detail Design

## Source Changes

`src/compiler/60.mir_opt/mir_opt/pattern/rule_engine.spl`:

- Add `OptimizerProviderKind.JitHotspot`.
- Add `optimization_rule_provider_is_runtime_hotspot`.
- Add `optimization_rule_provider_builtin_jit_hotspot`.

The helper constructs a built-in, hot, pipeline-pass provider so runtime hotspot providers do not accidentally use dynamic lookup or per-site table construction.

`src/compiler/95.interp/execution/tiered_jit.spl`:

- Add `JitHotspotPlan`.
- Add `jit_hotspot_profile_facts`.
- Add `jit_hotspot_plan_from_profile`.
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

## Tests

`test/unit/compiler/mir_opt/cipher/pattern_engine_spec.spl` adds a provider-contract test:

- JIT hotspot provider kind is `JitHotspot`.
- Load mode is built-in.
- Lookup kind is pipeline pass.
- Runtime hotspot predicate is true.
- Missing `safe_deopt` rejects execution.
- Providing all required facts allows execution.

`test/unit/compiler/interpreter/tiered_jit_hotspot_spec.spl` adds plan coverage:

- Cold profiles do not emit `profile.hot_count`.
- Hot typed profiles with safe deopt emit all required facts.
- Eligible plans require all runtime facts.
- Missing `safe_deopt` rejects planning without dropping hot-count facts.
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
