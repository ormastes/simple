<!-- codex-design -->
# Optimization Plugin JIT Hotspot Detail Design

## Source Changes

`src/compiler/60.mir_opt/mir_opt/pattern/rule_engine.spl`:

- Add `OptimizerProviderKind.JitHotspot`.
- Add `optimization_rule_provider_is_runtime_hotspot`.
- Add `optimization_rule_provider_builtin_jit_hotspot`.

The helper constructs a built-in, hot, pipeline-pass provider so runtime hotspot providers do not accidentally use dynamic lookup or per-site table construction.

## Tests

`test/unit/compiler/mir_opt/cipher/pattern_engine_spec.spl` adds a provider-contract test:

- JIT hotspot provider kind is `JitHotspot`.
- Load mode is built-in.
- Lookup kind is pipeline pass.
- Runtime hotspot predicate is true.
- Missing `safe_deopt` rejects execution.
- Providing all required facts allows execution.

## Documentation

Update:

- `doc/07_guide/compiler_optimization_plugin.md`
- `doc/04_architecture/simple_optimization_plugin.md`
- `doc/06_spec/app/compiler/feature/simple_optimization_plugin_spec.md`

The docs distinguish compiler rewrites from JIT hotspot plans.
