# Feature Request: Unified Optimizer Plugin System

**Date:** 2026-06-05
**Status:** Proposed
**Area:** compiler/mir_opt, compiler/tools/perf, compiler/interp/execution

## Problem

Three optimizer subsystems operate independently with no shared interface:

| Subsystem | Layer | Level | When |
|---|---|---|---|
| MIR optimizer (`60.mir_opt`) | `trait MirPass` + `DynamicPassRegistry` | MIR IR | Compile-time (static pipeline) |
| Optimizer plugin (`90.tools/perf/optimizer`) | Standalone CLI tool | Source text | Manual invocation only |
| Hotspot optimizer (`95.interp/execution/tiered_jit`) | Imports `mir_opt` directly, duplicates source-level heuristics inline | Both | Runtime (tiered JIT) |

**Consequences:**

1. Source-level heuristics are duplicated — `90.tools/perf/optimizer.spl` detects string-concat-in-loop, while `tiered_jit.spl` has its own `jit_hotspot_source_has_*` functions for the same patterns.
2. New optimization patterns must be added in up to 3 places.
3. Hotspot optimizer cannot leverage the source-level optimizer's analysis.
4. No way for users or the compiler driver to register custom optimization passes at either level.

## Proposed Design

### Common trait: `OptimizerPlugin`

```
trait OptimizerPlugin:
    fn name() -> text
    fn scope() -> PluginScope          # Mir | Source | Both
    fn level() -> OptLevel             # nil | Size | Speed | Aggressive
    fn apply_mode() -> ApplyMode       # Static | Dynamic | Both

    # MIR-level entry point (optional — default no-op)
    fn run_on_mir(module: MirModule, config: PluginConfig) -> OptResult

    # Source-level entry point (optional — default no-op)
    fn analyze_source(source: text, config: PluginConfig) -> List<OptSuggestion>

    # Cost estimate for hotspot budget decisions
    fn cost_class() -> text            # "cheap" | "moderate" | "expensive"
```

### ApplyMode

- **Static**: Registered in `OptimizationPipeline`, runs during every compilation at the configured `OptLevel`. Current MIR passes (DCE, const-fold, inline, etc.) become static plugins.
- **Dynamic**: Loaded/triggered at runtime by the hotspot optimizer when profiling data crosses a threshold. Current `jit_hotspot_source_has_*` heuristics become dynamic plugins.
- **Both**: Available in both modes. E.g., strength-reduction can run statically at compile time AND be re-applied dynamically with profile data.

### Registration

```
# Static — registered in pipeline at compile time
optimizer_pipeline_register(create_dce_plugin())
optimizer_pipeline_register(create_string_concat_plugin())

# Dynamic — registered in DynamicPassRegistry, triggered by hotspot
dynamic_pass_registry_register(create_vectorization_candidate_plugin())
dynamic_pass_registry_register(create_loop_strength_plugin())
```

Extends the existing `DynamicPassRegistry` + `ManifestPassEntry` system already in `60.mir_opt`.

### Hotspot integration

The tiered JIT's `jit_hotspot_rebuild_plan()` queries the unified registry:

```
# Instead of hardcoded jit_hotspot_source_has_* checks:
val applicable = dynamic_pass_registry_query(profile, backend, max_cost_class)
for plugin in applicable:
    if plugin.scope() == PluginScope.Source:
        val suggestions = plugin.analyze_source(source, config)
        # feed suggestions into rebuild plan
    if plugin.scope() == PluginScope.Mir:
        val result = plugin.run_on_mir(module, config)
        # apply MIR rewrites
```

### Migration path

1. **Phase 1**: Define `trait OptimizerPlugin` in `60.mir_opt`. Wrap existing `MirPass` implementations as `OptimizerPlugin` with `scope: Mir, apply_mode: Static`.
2. **Phase 2**: Refactor `90.tools/perf/optimizer.spl` patterns into `OptimizerPlugin` with `scope: Source, apply_mode: Both`. Delete duplicate `jit_hotspot_source_has_*` functions from `tiered_jit.spl`.
3. **Phase 3**: Update `tiered_jit.spl` to query the unified `DynamicPassRegistry` instead of hardcoded heuristics. The hotspot optimizer becomes a pure scheduler — no optimization logic of its own.
4. **Phase 4**: Expose plugin registration API so users can write custom optimizer plugins (e.g., domain-specific peephole patterns) loaded via manifest or `use` imports.

## Existing infrastructure to reuse

- `trait MirPass` (`60.mir_opt/mir_opt/mod.spl:84`) — becomes the MIR-level sub-interface
- `DynamicPassRegistry` + `dynamic_pass_registry_register` (`60.mir_opt/optimizer_manifest.spl`) — already supports runtime registration
- `ManifestPassEntry`, `OptimizerManifest` — manifest-driven pass configuration
- `OptimizationRuleProvider` + `OptimizerProviderKind` + backend policies (`60.mir_opt/mir_opt/pattern/rule_engine.spl`) — provider/policy pattern for backend-specific rules
- `PatternRule`, `PatternRuleSet` (`60.mir_opt/mir_opt/pattern/pattern_rule_pass.spl`) — reusable for source-level patterns too
- `OptLevel` enum — shared across all three subsystems already

## Diagram update

Updated in `doc/04_architecture/compiler/simple_compiler_arch.drawio`:
- Hotspot optimizer now connects to both MIR optimizer and optimizer plugin
- Reflects the unified plugin model where both are accessible through a common interface
