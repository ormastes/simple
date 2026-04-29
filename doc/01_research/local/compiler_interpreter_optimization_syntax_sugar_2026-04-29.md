# Local Research: Compiler/Interpreter Optimization + Syntax Sugar

**Date:** 2026-04-29
**Scope:** Current Simple compiler/interpreter optimization surface, syntax-sugar baseline, and local gaps that should drive feature requests.

## Summary

Simple already has meaningful groundwork in three areas:

1. **Backend optimization plumbing exists**
   - [`src/compiler/70.backend/backend/llvm_passes.spl`](../../../src/compiler/70.backend/backend/llvm_passes.spl) defines pass sets by optimization level.
   - Current pass inventory includes `InstCombine`, `SimplifyCFG`, `DeadCodeElimination`, `GVN`, `LICM`, `IndVarSimplify`, `LoopUnroll`, `LoopVectorize`, `SLPVectorize`, and `Inlining`.

2. **Rust seed/runtime already exposes release-profile tuning**
   - [`src/compiler_rust/Cargo.toml`](../../../src/compiler_rust/Cargo.toml) contains multiple profiles:
   - `release`: `opt-level=3`, `lto=false`, `codegen-units=16`
   - `release-opt`: `opt-level=3`, `lto="fat"`, `codegen-units=1`, `panic="abort"`
   - `bootstrap`: `opt-level="z"`, `lto="thin"`, `codegen-units=1`
   - The file also documents a manual PGO workflow using `-Cprofile-generate` and `-Cprofile-use`.

3. **Language-feature inventory already exists**
   - [`doc/01_research/domain/missing_language_features_2026-02-17.md`](../domain/missing_language_features_2026-02-17.md) says Simple already has a solid baseline including generics, pattern matching, Option/Result, async/await, closures, comprehensions, pipeline operators, effect annotations, and string interpolation.
   - That same doc already marks some feature areas as implemented or partially implemented, so this research should avoid duplicating older wishlists.

## Existing Optimization Work

### LLVM/native backend

- The backend is not starting from zero. There is already a named optimization-pass layer in [`src/compiler/70.backend/backend/llvm_passes.spl`](../../../src/compiler/70.backend/backend/llvm_passes.spl).
- This suggests that new requests should focus on:
  - measuring pass impact,
  - exposing profiles in product workflows,
  - startup/build-time visibility,
  - and optimization opportunities earlier than LLVM.

### Rust seed/runtime profiles

- The Rust compiler/runtime side already distinguishes:
  - faster compile profiles,
  - startup-oriented release profiles,
  - size-oriented bootstrap profiles.
- This means feature requests around **timing visibility**, **incremental artifacts**, and **PGO automation** fit naturally into the existing structure.

### Runtime startup and binary-size gaps

[`doc/bugs/runtime_size_bloat_followup.md`](../../bugs/runtime_size_bloat_followup.md) identifies a concrete startup and size problem:

- The runtime FFI dispatch table statically references built-ins at startup.
- Optional features like HTTP, regex, TLS, and hash helpers are pulled in unconditionally.
- The doc recommends feature-gating optional FFIs first, then potentially splitting the runtime into `simple_runtime_core` and `simple_runtime_extended`.
- The self-hosted linker path in [`src/compiler/70.backend/linker/linker_wrapper.spl`](../../../src/compiler/70.backend/linker/linker_wrapper.spl) must stay in sync with the Rust seed path.

This is important because it means some of the highest-value “optimization features” are not speculative compiler research; they are already visible local bottlenecks.

## Existing Syntax-Sugar Baseline

Based on local docs, Simple already has:

- pattern matching,
- closures,
- comprehensions,
- pipeline operators,
- string interpolation,
- named arguments,
- optional chaining,
- at least partial resource-management support.

Because of that, the best syntax-sugar requests are not “copy Python/JS/Rust wholesale”. They should target gaps that improve:

- compiler implementation readability,
- runtime lowering quality,
- module/loader clarity,
- and safe DSL or data construction.

## Local Gaps

I did **not** find strong evidence of the following as first-class local capabilities:

- adaptive interpreter specialization,
- inline caches,
- a tiered interpreter-to-mid-tier optimizer path,
- cross-session bytecode caching,
- compile-timing reports as a first-class product feature,
- structured template strings beyond current interpolation,
- import attributes or typed import metadata,
- Rust-style `let`-chain or guard sugar for nested lowering logic.

I also did not find a single local document that unifies:

- compiler throughput,
- interpreter hot-path optimization,
- startup/RSS targets,
- and syntax-sugar requests

into one prioritized backlog. This research fills that gap.

## Local Conclusions

### Highest-confidence optimization requests from repo state

1. Feature-gated optional runtime FFIs and/or runtime split.
2. Built-in compiler timing and hot-stage visibility.
3. Incremental or cached artifacts for repeated compile/tooling runs.
4. Earlier-stage optimization work before LLVM only where measurement shows payoff.

### Highest-confidence syntax-sugar requests from repo state

1. Let-chain and guard sugar for compiler/interpreter-heavy control flow.
2. Structured template strings for safe DSL generation.
3. Import attributes / typed imports for non-code assets.
4. Iterator-helper style lazy sequence ergonomics where they can desugar predictably.

## Feature-Request Backlog Seeds

- Adaptive opcode specialization with inline caches.
- Tier-2 micro-op or CFG/SSA middle IR for hot paths.
- Cross-session bytecode/module cache with strict invalidation.
- Compile timing report and stage-level profiling.
- Runtime FFI feature gating and lighter startup path.
- Let chains in `if` / `while`.
- `match` guards with pattern-bound names.
- Structured template strings.
- Import attributes.
- Lazy iterator helper surface desugared to loops.
