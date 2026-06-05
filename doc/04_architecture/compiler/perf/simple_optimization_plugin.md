# Simple Optimization Plugin Architecture

**Date:** 2026-05-13
**Status:** Draft

## Decision

Simple Optimization Plugin is the named extension point for reusable compiler and interpreter optimizations. The architecture favors built-in providers for hot and bootstrap-critical paths, with dynamic-library providers reserved for optional or experimental optimizers behind a stable manifest and ABI.

## Context

Simple already has several optimization surfaces: syntax desugaring, MIR optimization, MIR pattern rules, interpreter execution shortcuts, native build options, and LLVM backend optimization. Without a shared plugin contract, optimization work can drift into benchmark-specific rewrites or repeated lookup tables.

External compiler ecosystems support the same split:

- LLVM's new pass manager builds standard optimization pipelines and supports pass plugins.
- MLIR's pattern infrastructure models reusable rewrites with benefits, bounded recursion, and debug labels.

Simple should use those ideas without making every Simple optimizer an LLVM plugin. The first contract is language-aware and backend-independent.

## Layering

```text
CompilerOptions
  -> OptimizationRegistry
     -> BuiltinOptimizationProvider[]
     -> DynamicOptimizationProvider[]
        -> OptimizationPlan
           -> HIR passes
           -> MIR passes
           -> Pattern providers
           -> Interpreter providers
           -> JIT hotspot providers
           -> Backend metadata providers
```

## Core Interfaces

### OptimizationProvider

Common provider metadata:

- `name`
- `version`
- `kind`
- `load_mode`
- `lookup_kind`
- `hot_path`
- `enabled`
- `target_filter`
- `required_facts`
- `produced_facts`
- `safety_class`

### OptimizationPlan

Per-compile plan derived from optimization level, target, backend, debug mode, and feature gates.

Responsibilities:

- choose providers;
- order passes;
- reject incompatible dynamic plugins;
- expose a deterministic plan for diagnostics;
- provide stats for benchmark and regression analysis.

### RuleLookup

Lookup providers must declare how they find rules:

- direct exact checks for small hot rule sets;
- prebuilt immutable indexes for larger stable sets;
- dynamic lookup only outside per-site hot loops or after caching;
- whole-pass traversal for module/function transforms.

## Built-in vs Dynamic

| Property | Built-in | Dynamic library |
|----------|----------|-----------------|
| Startup latency | lowest | load/manifest cost |
| Bootstrap suitability | yes | no |
| Hot-path use | yes | only after cached |
| Internal MIR access | direct | stable ABI only |
| Security surface | compiler-owned | requires validation |
| Best use | stable general optimizations | optional experiments/out-of-tree target rules |

## Invariants

- Optimizations are optional: disabling a provider preserves behavior.
- Facts are explicit: no pass may assume aliasing, overflow, pointer, or target facts that were not proven.
- Hot providers allocate no per-lookup rule tables.
- Dynamic providers cannot be required for bootstrap.
- Backend-specific optimization does not replace Simple MIR/HIR semantic optimization.

## Current Implementation Anchors

- MIR optimizer: `src/compiler/60.mir_opt/mir_opt/`
- Pattern engine: `src/compiler/60.mir_opt/mir_opt/pattern/`
- Rule provider primitives: `src/compiler/60.mir_opt/mir_opt/pattern/rule_engine.spl`
- Cipher pattern provider: `src/compiler/60.mir_opt/mir_opt/pattern/rules_crypto.spl`
- JIT integration docs: `doc/04_architecture/runtime/jit_interpreter_integration.md`
- Dynamic library runtime reference: `doc/07_guide/dynlib_api.md`

## JIT Hotspot Providers

`jit-hotspot` providers use the same metadata contract as compiler optimization
providers, but their required facts come from runtime profiling and guard
analysis rather than compile-only analysis. A hotspot provider is eligible only
when facts such as `profile.hot_count`, `typed_mir`, and `safe_deopt` are
available.

The provider output is a plan, not an unconditional rewrite. The JIT execution
manager may compile or specialize the hot region, while the interpreter/native
fallback remains authoritative if guards fail, profile data ages out, or the
provider is disabled by optimization level. Dynamic hotspot providers must be
loaded outside the dispatch hot path and cached before they can participate in
runtime planning.

The tiered JIT manager derives the initial runtime facts from function profiles:
when a function reaches its tier threshold it may emit `profile.hot_count`; type
lowering contributes `typed_mir`; deoptimization analysis contributes
`safe_deopt`. These facts form a `JitHotspotPlan`, which is pure planning data
until a runtime backend chooses to compile or specialize the function.

## Compression Provider

The pure Simple LZ4/Zstd work uses this architecture through a built-in
`CompressionPatternProvider`. The provider is behavior-preserving and targets
compiler/JIT hot loops that are common across compression codecs:

- typed `[u8]` load/store loops;
- literal-copy loops;
- match-copy loops with overlap semantics;
- bitstream reader loops for Zstd FSE/HUF decode;
- static decode-table materialization;
- length and bounds facts for source/destination slices.

The provider must not be a codec implementation. LZ4 and Zstd source remains in
`src/lib/common/compress`; the provider only lowers proven loop and table
patterns. Disabling it must preserve compressed bytes, decompressed bytes,
typed errors, and checksums.

The first plan using this provider is
`doc/03_plan/agent_tasks/pure_simple_lz4_zstd_speed_parity.md`.

## Unified OptimizerPlugin Trait

All three optimizer subsystems converge on a common `OptimizerPlugin` trait:

```text
trait OptimizerPlugin:
    fn name() -> text
    fn scope() -> PluginScope          # Mir | Source | Both
    fn apply_mode() -> ApplyMode       # Static | Dynamic | Both
    fn level() -> OptLevel
    fn run_on_mir(module, config) -> OptResult       # MIR-level (optional)
    fn analyze_source(source, config) -> [OptSuggestion]  # Source-level (optional)
    fn cost_class() -> text            # "cheap" | "moderate" | "expensive"
```

**Static plugins** run during every compilation in the `OptimizationPipeline`. Current `MirPass` implementations (DCE, inline, const-fold, etc.) become static plugins.

**Dynamic plugins** are loaded/triggered at runtime by the hotspot optimizer when profiling data crosses a threshold. Current `jit_hotspot_source_has_*` heuristics become dynamic plugins.

**Both-mode plugins** (e.g., strength-reduction) run statically at compile time and can be re-applied dynamically with richer profile data.

The hotspot optimizer becomes a pure scheduler that queries the unified `DynamicPassRegistry` — no optimization logic of its own.

See: `doc/02_requirements/feature/unified_optimizer_plugin.md`

## Roadmap

1. Keep hot built-in pattern providers on direct or indexed lookup.
2. Add registry-level planning and diagnostics for selected providers.
3. Add immutable indexed lookup for large rule sets.
4. Define a dynamic provider manifest and ABI.
5. Add benchmark counters for provider load time, lookup hits/misses, rewrite count, and compile-time overhead.
6. Add built-in compression loop/table providers for LZ4/Zstd parity before
   allowing dynamic compression plugins.
7. Add optional LLVM pass-plugin bridging only for providers that genuinely need LLVM IR pass insertion.
8. Unify MIR optimizer, source-level optimizer, and hotspot optimizer behind the
   `OptimizerPlugin` trait (see unified_optimizer_plugin feature request).
9. Refactor `jit_hotspot_source_has_*` functions into `OptimizerPlugin` instances
   with `scope: Source, apply_mode: Dynamic`, eliminating duplication with
   `90.tools/perf/optimizer.spl`.

## References

- LLVM New Pass Manager: https://llvm.org/docs/NewPassManager.html
- LLVM new pass plugins: https://llvm.org/docs/WritingAnLLVMNewPMPass.html
- MLIR Pattern Rewriter: https://mlir.llvm.org/docs/PatternRewriter/
- MLIR Declarative Rewrite Rules: https://mlir.llvm.org/docs/DeclarativeRewrites/
- Unified optimizer plugin feature request: `doc/02_requirements/feature/unified_optimizer_plugin.md`
- Architecture diagram: `doc/04_architecture/compiler/simple_compiler_arch.drawio`
