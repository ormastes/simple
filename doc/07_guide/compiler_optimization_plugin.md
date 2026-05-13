# Simple Optimization Plugin Guide

**Date:** 2026-05-13
**Status:** Draft contract

## Purpose

A **Simple Optimization Plugin** is a reusable optimizer extension for the Simple compiler and interpreter pipeline. It packages a general optimization rule, pass, or provider so similar programs can gain performance without each application carrying local ad hoc rewrites.

The plugin contract is for Simple's own optimization layers first:

```text
source -> shared frontend -> HIR -> MIR -> Simple Optimization Plugin passes
       -> interpreter/native lowering -> LLVM IR/backend, bytecode, or runtime execution
```

LLVM pass plugins are a separate backend mechanism. Simple Optimization Plugins may improve the LLVM path by producing better MIR or better LLVM IR facts, but they are not required to be LLVM plugins.

## What Belongs In A Plugin

Use a Simple Optimization Plugin for transformations that are:

- General across many programs, not only one benchmark.
- Semantics-preserving under Simple language rules.
- Expressible over HIR, MIR, pattern idioms, interpreter dispatch, or backend-independent metadata.
- Measurable with before/after tests or benchmarks.
- Safe to disable without changing observable program behavior except speed, code size, or diagnostics.

Good examples:

- Constant folding, copy propagation, dead code elimination.
- Strength reduction such as `% power_of_two` to bitmask when integer semantics allow it.
- Pattern idiom rules such as replacing recognized byte/crypto loops with proven runtime-free lowering.
- Search/match indexing for repeated exact-symbol rule lookup.
- Bounds-check elimination when range facts prove safety.
- Interpreter dispatch caching for repeated stable call or pattern sites.

Bad examples:

- A rewrite that depends on one source file name or benchmark fixture.
- A transformation that changes overflow, panic, aliasing, or memory-order semantics.
- A pass that lies through attributes such as `nonnull`, `noalias`, `noundef`, `nsw`, or `nuw`.
- A dynamic plugin loaded in a hot path when a built-in provider is required for startup or compile latency.

## Plugin Kinds

| Kind | Stage | Typical use |
|------|-------|-------------|
| `syntax` | frontend normalization | sugar desugaring that preserves shared frontend behavior |
| `hir` | HIR | type-aware simplification before MIR construction |
| `mir` | MIR | general compiler optimizations and semantic rewrites |
| `pattern` | MIR pattern engine | idiom recognition, exact-symbol lookup, intrinsic replacement |
| `interpreter` | interpreter runtime | dispatch caches and evaluated-form specialization |
| `backend-metadata` | backend boundary | target-independent facts that help LLVM or native lowering |

## Load Modes

Simple uses two load modes.

### Built-in

Built-in providers are compiled into the compiler/interpreter. Use this for hot, stable, security-sensitive, or bootstrap-critical optimizations.

Built-in providers should be the default for:

- optimizer passes used by normal `simple check`, `simple test`, `simple compile`, or `simple native-build`;
- exact-symbol or pattern lookup on hot paths;
- passes required during bootstrap;
- passes that need access to internal MIR invariants.

### Dynamic library

Dynamic providers are loaded from a library or SMF artifact through a manifest and a stable ABI. Use this for optional, experimental, target-specific, or out-of-tree optimizations.

Dynamic providers must not be required for bootstrap or normal release builds. A missing dynamic provider must degrade to "optimization unavailable", not a wrong-code fallback.

## Provider Metadata

Every provider should declare:

| Field | Meaning |
|-------|---------|
| `name` | stable provider identifier, for example `simple.opt.crypto.cipher_rules` |
| `version` | semantic provider version |
| `kind` | `syntax`, `hir`, `mir`, `pattern`, `interpreter`, or `backend-metadata` |
| `load_mode` | `builtin` or `dynamic-library` |
| `lookup_kind` | `direct-exact`, `indexed-exact`, `dynamic-exact`, or `pipeline-pass` |
| `hot_path` | whether the provider is expected in compile/interpreter hot paths |
| `target_filter` | optional architecture, OS, ABI, or backend constraints |
| `required_facts` | facts needed before the pass may run |
| `produced_facts` | facts exposed to later passes |
| `safety_class` | `pure`, `target-aware`, `unsafe-facts`, or `experimental` |

## Lookup Strategy

Provider lookup is part of the performance contract.

- Use `direct-exact` for tiny hot sets where explicit equality checks are faster and allocate nothing.
- Use `indexed-exact` for larger stable rule sets that should build one map or trie once.
- Use `dynamic-exact` for optional out-of-tree providers where the call boundary is acceptable.
- Use `pipeline-pass` for whole-module or whole-function passes that do not run per call site.

Do not rebuild rule tables for each lookup. Rule tables are constructed once per provider, compiled into direct lookup code, or held in an immutable index.

## Pass Lifecycle

1. Register provider metadata.
2. Check feature gates, target filters, and optimization level.
3. Verify required facts are available.
4. Run the provider over the smallest useful scope.
5. Record hit/miss/change statistics.
6. Verify preserved and produced facts.
7. Run downstream validation or benchmark gates.

## Optimization Levels

Simple Optimization Plugins are selected by Simple optimization level before backend-specific optimization.

| Level | Plugin policy |
|-------|---------------|
| `none` | disabled except verifier-only passes |
| `basic` | cheap canonicalization and diagnostics-safe rules |
| `standard` | default general MIR/pattern/interpreter improvements |
| `aggressive` | costlier whole-function/module optimization and vectorization-friendly rewrites |
| `size` | code-size-biased rules only |

LLVM optimization still uses LLVM's default pass pipelines for backend work. Simple Optimization Plugins should improve the IR facts and structure that LLVM receives, not duplicate LLVM CPU backend work.

## Safety Rules

- The plugin may not change observable semantics.
- The plugin must not introduce runtime library dependency changes unless its manifest declares them.
- The plugin must not emit stronger facts than Simple semantics prove.
- The plugin must preserve debug behavior at `none` and debug-focused modes.
- Dynamic plugins must be version-checked before load and isolated from bootstrap-critical paths.
- Unsafe or experimental providers must be disabled by default.

## Validation Checklist

Every production plugin needs:

- unit tests for enabled and disabled behavior;
- negative tests proving unsafe patterns are not rewritten;
- compiler check coverage for affected modules;
- interpreter or native smoke tests if runtime execution changes;
- benchmark evidence for performance claims;
- stats proving the provider is not rebuilding indexes or tables in a hot loop.

For LLVM-affecting paths, also run IR verification when IR dump support is available:

```bash
opt -verify input.ll -o /dev/null
opt -verify-each -passes='default<O2>' input.ll -o output.bc
```

## Minimal Example

```text
provider:
  name: simple.opt.math.strength_reduce
  kind: mir
  load_mode: builtin
  lookup_kind: pipeline-pass
  hot_path: true
  required_facts: [integer_widths, overflow_policy]
  produced_facts: [canonical_integer_arithmetic]

rule:
  before: x % C
  when: C is a power of two and x is unsigned or non-negative by fact
  after: x & (C - 1)
```

This is a valid Simple Optimization Plugin because the rule applies to many programs, depends on declared facts, is semantics-preserving only under those facts, and improves both interpreter and backend lowering opportunities.

## Related Docs

- [Compiler Optimization Levels](compiler_optimization_levels.md)
- [LLVM Optimization Workflow](backend/llvm_optimization_workflow.md)
- [Dynamic Library API Guide](dynlib_api.md)
- [Simple Optimization Plugin Architecture](../04_architecture/simple_optimization_plugin.md)
- [Simple Optimization Plugin Spec](../06_spec/app/compiler/feature/simple_optimization_plugin_spec.md)
