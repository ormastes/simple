# Simple Optimization Plugin Specification

**Status:** Draft
**Updated:** 2026-05-13
**Category:** Compiler optimization

## Summary

Simple Optimization Plugin defines the common contract for reusable compiler, interpreter, and JIT hotspot optimization providers. It covers built-in and dynamic load modes, metadata, lookup strategies, safety rules, validation, and performance evidence.

## Feature IDs

| ID | Requirement |
|----|-------------|
| SOP-001 | The compiler shall name the reusable optimizer extension point `Simple Optimization Plugin`. |
| SOP-002 | A provider shall declare metadata including name, version, kind, load mode, lookup kind, hot-path flag, required facts, produced facts, and safety class. |
| SOP-003 | Built-in providers shall be allowed on bootstrap and compile/interpreter hot paths. |
| SOP-004 | Dynamic-library providers shall be optional and version checked before load. |
| SOP-005 | Missing dynamic providers shall not change program semantics. |
| SOP-006 | Rule lookup shall avoid rebuilding tables per call-site lookup. |
| SOP-007 | Providers shall run only when required semantic facts are available. |
| SOP-008 | Providers shall emit stats for hits, misses, rewrites, and compile-time cost where applicable. |
| SOP-009 | Providers shall be disabled by optimization level or feature gate without changing observable behavior. |
| SOP-010 | Providers that affect LLVM output shall preserve valid IR and target facts. |
| SOP-011 | JIT hotspot providers shall require runtime profile and safe-deoptimization facts before producing a hotspot plan. |
| SOP-012 | Disabling or invalidating a JIT hotspot provider shall preserve interpreter/native fallback behavior. |
| SOP-013 | Tiered JIT profile data shall expose `profile.hot_count` through a testable hotspot planning API. |
| SOP-014 | JIT hotspot planning performance evidence shall use a benchmark that covers cold, ready, and invalidated plans. |
| SOP-015 | Tiered JIT promotion shall consume eligible hotspot plans without requiring Rust execution-manager API changes. |
| SOP-016 | JIT hotspot specialization shall require eligible plans, specialized source, and declared semantic proof before replacing compile input. |

## Provider Kinds

| Kind | Scope |
|------|-------|
| `syntax` | shared frontend normalization |
| `hir` | type-aware high-level optimization |
| `mir` | backend-independent optimization |
| `pattern` | idiom and exact-symbol rewrite rules |
| `interpreter` | interpreter dispatch and evaluated-form optimization |
| `jit-hotspot` | runtime hotspot planning from profile facts and safe deopt guards |
| `backend-metadata` | target-independent facts for backend lowering |

## Load Modes

### Built-in

Built-in providers are linked into the compiler/interpreter and may access internal optimizer data structures. They are required for hot, stable, or bootstrap-critical optimizations.

### Dynamic library

Dynamic providers are loaded through a manifest and stable ABI. They are not part of the bootstrap-critical path and must be optional.

## Lookup Kinds

| Lookup kind | Requirement |
|-------------|-------------|
| `direct-exact` | Use explicit direct matching for tiny hot sets. |
| `indexed-exact` | Build an immutable index once for larger stable sets. |
| `dynamic-exact` | Cache dynamic lookups before repeated use. |
| `pipeline-pass` | Traverse module/function/block scope instead of per-site lookup. |

## Acceptance Criteria

- AC-SOP-001: Documentation defines the term in the architecture glossary.
- AC-SOP-002: User guide explains when to use built-in vs dynamic providers.
- AC-SOP-003: Architecture doc defines registry, provider, plan, and lookup responsibilities.
- AC-SOP-004: Spec lists safety and validation requirements.
- AC-SOP-005: Existing optimization-level docs cross-link the guide.
- AC-SOP-006: A provider implementation shall have tests for enabled behavior, disabled behavior, unsafe negative cases, lookup stats, and required-fact rejection.
- AC-SOP-007: Performance claims shall include representative benchmark evidence.
- AC-SOP-008: JIT hotspot providers shall document guard facts, fallback behavior, and invalidation semantics.

## Non-Goals

- Do not replace LLVM's target backends.
- Do not require every Simple optimizer to be an LLVM pass plugin.
- Do not make dynamic plugins mandatory for release builds or bootstrap.
- Do not accept benchmark-specific source rewrites as production optimizer plugins.

## Validation Commands

Documentation validation:

```bash
test -f doc/07_guide/compiler_optimization_plugin.md
test -f doc/04_architecture/simple_optimization_plugin.md
test -f doc/06_spec/app/compiler/feature/simple_optimization_plugin_spec.md
rg -n "Simple Optimization Plugin" doc/04_architecture/glossary.md doc/07_guide/README.md
```

Implementation validation for providers:

```bash
bin/simple test test/unit/compiler/mir_opt/cipher/pattern_engine_spec.spl --mode=interpreter
bin/simple test test/unit/compiler/interpreter/tiered_jit_hotspot_spec.spl --mode=interpreter
bin/simple run test/perf/compiler/jit_hotspot_plan_bench.spl --mode=interpreter
bin/simple check src/compiler/60.mir_opt
```

LLVM-affecting providers should additionally verify generated IR when available:

```bash
opt -verify input.ll -o /dev/null
opt -verify-each -passes='default<O2>' input.ll -o output.bc
```

## Traceability

- Guide: `doc/07_guide/compiler_optimization_plugin.md`
- Architecture: `doc/04_architecture/simple_optimization_plugin.md`
- Glossary: `doc/04_architecture/glossary.md`
- Optimization levels: `doc/07_guide/compiler_optimization_levels.md`
