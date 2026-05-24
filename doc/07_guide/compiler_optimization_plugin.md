# Simple Optimization Plugin Guide

**Date:** 2026-05-13
**Status:** Draft contract

## Purpose

A **Simple Optimization Plugin** is a reusable optimizer extension for the Simple compiler and interpreter pipeline. It packages a general optimization rule, pass, or provider so similar programs can gain performance without each application carrying local ad hoc rewrites.

The plugin contract is for Simple's own optimization layers first:

```text
source -> shared frontend -> HIR -> MIR -> Simple Optimization Plugin passes
       -> interpreter/native lowering -> LLVM IR/backend, bytecode, or runtime execution
       -> JIT hotspot specialization when runtime profile facts prove a site is hot
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
- JIT hotspot specialization for repeatedly executed MIR/function regions when profile counts, type facts, and deoptimization safety are available.

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
| `jit-hotspot` | JIT runtime planning | hot-loop/function specialization using profile facts and safe deopt guards |
| `backend-metadata` | backend boundary | target-independent facts that help LLVM or native lowering |

Graphics and rendering providers use the same plugin contract. Examples include
shader specialization, pipeline-cache keys, CPU SIMD vectorization facts, CUDA
kernel specialization, Vulkan/Metal/WebGPU layout compatibility, and web-renderer
paint-fragment lowering facts. These providers should be reusable by the 2D
engine, 2D game engine, 3D engine, 3D game engine, web renderer, GUI library,
and window manager instead of being duplicated in each renderer.

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

For persistent backend optimization, providers should also define a stable state
key:

```text
provider_id + provider_version + target_triple + backend_kind
  + session_mode + session_policy_hash + produced_fact_schema
```

`ManagedShared` providers may retain warm caches across app frames. `PerfExclusive`
providers must use isolated mutable state so benchmark results do not include
managed-session warmup, queues, allocators, or counters. Immutable capability
tables may be shared when the target and backend feature records are identical.

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

## How To Write A Plugin

Start with the smallest built-in provider that proves the optimization is general. Move to dynamic loading only after the provider contract, tests, and benchmark evidence are stable.

1. Define the optimization shape.

   Write the transformation as a before/after rule and list the semantic facts it needs. If the rule cannot be explained without naming one benchmark file, it is not ready to become a Simple Optimization Plugin.

   ```text
   before: local = x % 128
   facts: 128 is a power of two; x is unsigned or proven non-negative
   after: local = x & 127
   ```

2. Pick the stage.

   Use `mir` for general arithmetic, data-flow, and control-flow rewrites. Use `pattern` for recognized call/idiom replacement. Use `interpreter` only when the optimization changes dispatch or evaluated-form caching without changing language semantics. Use `jit-hotspot` only for runtime-selected hot regions where profiling proves the site is worth compiling or specializing.

3. Add provider metadata.

   Built-in hot providers should be represented in compiler source with metadata equivalent to:

   ```text
   name: simple.opt.<domain>.<rule_set>
   kind: mir | pattern | interpreter | jit-hotspot
   load_mode: builtin
   lookup_kind: direct-exact | indexed-exact | pipeline-pass
   hot_path: true
   required_facts: [...]
   produced_facts: [...]
   safety_class: pure | target-aware
   ```

   For current MIR pattern work, place shared provider primitives in `src/compiler/60.mir_opt/mir_opt/pattern/rule_engine.spl` and domain rule providers beside the pattern implementation, for example `rules_crypto.spl`.

4. Implement lookup or traversal.

   Choose the lookup form before coding:

   - `direct-exact`: write direct equality checks and construct only the matched rule.
   - `indexed-exact`: build an immutable index once, then reuse it.
   - `pipeline-pass`: traverse module/function/block scope once per pass.
   - `dynamic-exact`: load once, version-check once, and cache repeated symbol lookups.

   Hot lookup functions must not build a whole rule table per call-site lookup.

5. Gate the pass.

   Add an early no-op guard when provider metadata or target capabilities prove no rewrite can apply. A pass that cannot change the module should return the original module before walking functions and blocks.

6. Preserve semantics.

   Do not rewrite unless the required facts are present. Do not attach stronger LLVM or MIR facts than Simple semantics prove. In particular, do not invent `noalias`, `nonnull`, `noundef`, `nsw`, `nuw`, or fast-math behavior to get a benchmark win.

   JIT hotspot providers also need runtime guard facts. A hotspot provider must require facts such as `profile.hot_count`, `typed_mir`, and `safe_deopt`; it may produce a plan such as `jit.hotspot_plan`, but it must preserve the interpreter/native fallback path and invalidate the plan when guards fail.

   In the tiered JIT path, call counts and thresholds produce `profile.hot_count`; typed MIR availability produces `typed_mir`; safe deoptimization analysis produces `safe_deopt`. The resulting hotspot plan is data until a runtime backend compiles or specializes it.

   Tiered JIT promotion consumes eligible plans before native compilation. The first consumer is deliberately conservative: it records that the plan was accepted and selects the compile input, but falls back to the original source when the provider is disabled or facts are incomplete.

7. Test enabled, disabled, and unsafe cases.

   Add unit tests for:

   - the provider metadata;
   - positive rewrite behavior;
   - disabled/no-capability behavior;
   - unknown or unsafe input that must not rewrite;
   - lookup stats or no-op fast path behavior when the provider is hot.

8. Prove performance only after parity.

   First prove output/checksum parity. Then benchmark the representative workload and record compile-time or runtime impact. For JIT hotspot providers, benchmark planning separately from native code emission so `profile.hot_count` fact extraction, plan invalidation, and backend specialization costs do not get collapsed into one number. A plugin is accepted as a general optimization only when the evidence applies beyond one local fixture.

## Built-in Plugin Skeleton

```text
fn my_rule_provider() -> OptimizationRuleProvider:
    optimization_rule_provider_builtin("simple.opt.domain.my_rules", true)

fn lookup_my_rule(symbol: text) -> Rule?:
    if symbol == "std.domain.hot_function":
        return Some(create_rule("match_hot_function", "domain_intrinsic", "domain_feature", -3))
    nil

fn run_my_pattern_pass(module: MirModule, target: TargetCapsKind, remarks: bool) -> MirModule:
    if not remarks and not caps_kind_supports_any_pattern_idiom(target):
        return module
    # Walk only the smallest scope needed, then rewrite when lookup + facts pass.
    module
```

## Dynamic Plugin Manifest Sketch

Dynamic loading is a future ABI boundary, not the default for hot compiler paths. A dynamic provider should declare enough information for the compiler to reject incompatible plugins before execution:

```text
simple_optimization_plugin:
  name: simple.opt.vendor.experimental
  version: 0.1.0
  simple_abi: 1
  kind: pattern
  lookup_kind: dynamic-exact
  target_filter: [x86_64-v3, x86_64-v4]
  required_facts: [typed_mir, target_caps]
  produced_facts: [canonical_intrinsics]
  entry_symbol: simple_opt_plugin_register
  safety_class: experimental
```

Dynamic providers must be optional. If the library is missing, ABI-incompatible, or rejected by target filters, the compiler continues without that optimization.

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
