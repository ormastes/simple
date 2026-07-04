<!-- codex-research -->
# Optimization Plugin JIT Hotspot Local Research

Date: 2026-05-24

## Existing Surfaces

- `doc/07_guide/compiler_optimization_plugin.md` already defines Simple Optimization Plugin as the common optimizer extension point for compiler and interpreter work.
- `doc/04_architecture/compiler/perf/simple_optimization_plugin.md` defines provider metadata, built-in vs dynamic providers, optimization plans, and lookup responsibilities.
- `doc/06_spec/app/compiler/feature/simple_optimization_plugin_spec.md` lists requirements and validation commands for the plugin contract.
- `src/compiler/60.mir_opt/mir_opt/pattern/rule_engine.spl` provides the current in-source provider schema:
  - `OptimizerProviderKind`
  - `OptimizationRuleProvider`
  - required/produced facts
  - lookup kind
  - hot path flag
  - fact gating helpers
- `doc/04_architecture/runtime/jit_interpreter_integration.md` and `doc/04_architecture/runtime/jit_index.md` describe the JIT interpreter path and execution manager, but they were not tied into the optimization plugin provider taxonomy.

## Gap

The plugin contract covered compiler/MIR/pattern/interpreter providers but did not name JIT hotspot optimization as a first-class provider kind. That left runtime profile-driven optimization outside the reusable provider model.

## Chosen Slice

Add `jit-hotspot` as a provider kind in the shared provider schema and document its required runtime facts:

- `profile.hot_count`
- `typed_mir`
- `safe_deopt`

The first implementation is a contract/schema slice, not a backend JIT compiler rewrite. It makes JIT hotspot optimization plannable and testable through the same provider metadata and fact-gating machinery as compiler optimizations.
