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
- Dynamic library runtime reference: `doc/07_guide/dynlib_api.md`

## Roadmap

1. Keep hot built-in pattern providers on direct or indexed lookup.
2. Add registry-level planning and diagnostics for selected providers.
3. Add immutable indexed lookup for large rule sets.
4. Define a dynamic provider manifest and ABI.
5. Add benchmark counters for provider load time, lookup hits/misses, rewrite count, and compile-time overhead.
6. Add optional LLVM pass-plugin bridging only for providers that genuinely need LLVM IR pass insertion.

## References

- LLVM New Pass Manager: https://llvm.org/docs/NewPassManager.html
- LLVM new pass plugins: https://llvm.org/docs/WritingAnLLVMNewPMPass.html
- MLIR Pattern Rewriter: https://mlir.llvm.org/docs/PatternRewriter/
- MLIR Declarative Rewrite Rules: https://mlir.llvm.org/docs/DeclarativeRewrites/
