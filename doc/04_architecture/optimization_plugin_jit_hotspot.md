<!-- codex-design -->
# Optimization Plugin JIT Hotspot Architecture

## Decision

Extend the existing Simple Optimization Plugin contract with a `jit-hotspot` provider kind. This keeps compiler optimizations, interpreter optimizations, and runtime hotspot optimization under one provider model instead of creating a separate JIT-only framework.

## Provider Shape

JIT hotspot providers use:

- `kind = JitHotspot`
- `load_mode = Builtin` for hot/runtime-critical providers
- `lookup_kind = PipelinePass`
- `hot_path = true`
- required facts such as `profile.hot_count`, `typed_mir`, and `safe_deopt`
- produced facts such as `jit.hotspot_plan`
- `safety_class = runtime-guarded`

## Runtime Semantics

A JIT hotspot provider produces a plan. It does not replace program semantics:

- The interpreter/native fallback remains valid.
- Guards decide whether the compiled/specialized path can run.
- Missing facts disable the provider without changing behavior.
- Dynamic providers, when introduced later, must be loaded and cached outside the dispatch hot path.

## Implementation Anchor

The contract lives in `src/compiler/60.mir_opt/mir_opt/pattern/rule_engine.spl` because that file already owns provider metadata, load mode, lookup kind, fact gating, and provider stats.

Runtime hotspot facts are exposed from `src/compiler/95.interp/execution/tiered_jit.spl`. The tiered JIT owns function call counts and tier thresholds, so it is the correct boundary for deriving `profile.hot_count` before optimizer providers consume the fact.

The tiered JIT exposes a data-only `JitHotspotPlan`. This keeps planning separate from native code emission: unit tests can verify eligibility, missing facts, and invalidation without calling `rt_jit_*` externs, while the runtime can later use the same plan to choose a specialized native path.

`TieredJitManager.record_call` consumes the plan at the tier-1 promotion boundary. The consumer currently selects the compile source and records whether a hotspot plan was accepted; original-source compilation remains the fallback when the provider is disabled or required facts are missing. Rust `ExecutionManager` stays unchanged until a backend needs specialization-specific plan fields.

Specialized source replacement is opt-in through `JitHotspotSpecializationProvider`. A provider may replace the compile source only when the plan is eligible, the provider is enabled, a non-empty specialized source is present, and the provider declares a semantic proof. This makes the first concrete hotspot optimization path useful without letting arbitrary runtime profile data rewrite code by itself.
