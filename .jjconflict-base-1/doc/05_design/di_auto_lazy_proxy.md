# Auto-Lazy DI with Interface-Based Proxy Generation

**Status:** Implemented
**Date:** 2026-02-19
**Category:** Infrastructure / Runtime

## Overview

The full MCP server (`src/app/mcp/main.spl`) eagerly imports `helpers.spl` which pulls in `std.mcp_sdk.core.json`, `jsonrpc`, and `types` -- adding ~100-150ms to startup. While `use lazy` already defers 34 tool handlers (40x speedup), the core SDK chain remains eager because the protocol dispatch loop needs JSON helpers on every request.

This design adds a DI system where:
1. SDN config controls lazy/eager per profile (dev=eager, prod=lazy, test=eager)
2. Interface-based types get auto-generated lazy proxies at the desugar level
3. Lazy instantiation cascades work in interpreter mode
4. The full MCP server's helpers.spl chain becomes lazy via DI

## Cross-Language Research

### Kotlin Lazy Delegates
Kotlin's `by lazy {}` delegates evaluation to first access. Thread-safe by default (SYNCHRONIZED mode). The value is computed once and cached. Pattern: `val service: Service by lazy { createService() }`.

### Spring @Lazy
Spring's `@Lazy` annotation defers bean creation until first use. Creates a proxy object at injection time that delegates to the real bean. Works with constructor injection via `@Lazy` parameter annotation. Profile-based configuration via `@Profile`.

### Dagger Lazy<T>
Dagger wraps providers in `Lazy<T>` which defers `.get()` to first call. The provider is called once, result cached. No proxy generation -- requires explicit `.get()` calls at each use site.

### .NET Lazy<T>
`System.Lazy<T>` defers value creation to `.Value` access. Thread-safe with configurable modes (LazyThreadSafetyMode). Supports exception caching. No proxy transparency.

### Python PEP 810 (Accepted Nov 2025)
Explicit lazy imports: `lazy import module`. Module loaded on first attribute access. Import statement records intent, actual loading deferred. Profile-driven via importlib configuration.

### Haskell Thunks
All values lazy by default. Thunks represent unevaluated computations. Forced on pattern match or `seq`. GHC optimizes via strictness analysis. No explicit proxy -- laziness is the default evaluation strategy.

## Interface-Based Proxy Pattern

### Virtual Proxy (GoF)
A proxy implements the same interface as the real service. Method calls are forwarded to the real instance, which is created on first access. The proxy is indistinguishable from the real service to callers.

### Java ClassLoader Lazy Loading
Classes loaded on first use. The JVM creates proxy stubs that trigger class loading when methods are called. Similar to our approach but at bytecode level.

### How It Works in Simple

Simple's trait desugar transforms traits into structs with fn-fields:

```simple
trait JsonService:
    fn escape(s: text) -> text
    fn js(s: text) -> text
```

Becomes:

```simple
struct JsonService:
    escape_fn: fn(text) -> text
    js_fn: fn(text) -> text
```

A lazy proxy is simply a `JsonService` struct where each fn-field delegates to `_di_force_service()` before calling the real method. No new runtime types needed.

## Why `lazy val` Is Insufficient

`lazy val` (from `lazy_val.spl`) covers singletons and chains but NOT:
- **Factories/Pools**: Need per-call creation, not singleton caching
- **Proxy transparency**: `lazy val` requires `.force()` at every call site
- **Profile-based config**: No way to switch eager/lazy per environment
- **Cascade resolution**: No automatic transitive dependency resolution

Auto-proxy at desugar level provides transparent lazy delegation without modifying call sites.

## Runtime Constraints

Simple's runtime has constraints that shape the design:
- **NO try/catch/throw**: Use Option pattern, nil returns, error flags
- **NO generics at runtime**: `<>` syntax fails in interpreter
- **Nested closure capture**: Can READ outer vars, CANNOT MODIFY
- **Chained methods broken**: Use intermediate vars

### Design Consequences
- Mutable state uses module-level Dicts (not closures)
- Cycle detection via "initializing" flag (like LazyStatus.Evaluating)
- Named delegation functions instead of lambdas (no capture issues)
- Proxy is a regular struct (no new interpreter value types)

## Profile-Based Configuration

```
dev  = eager (fail-fast, immediate error reporting)
prod = lazy  (fast startup, ~30-50% reduction in time-to-first-response)
test = eager (predictable, deterministic behavior)
```

Per-service override:
- `lazy: auto` -- defers to profile default
- `lazy: true` -- always lazy regardless of profile
- `lazy: false` -- always eager regardless of profile

## Cascade Mechanism

When `_di_force_service("protocol")` is called:
1. Factory `create_protocol_state()` runs
2. Factory calls `di_resolve("json_helpers")` internally
3. This triggers `_di_force_service("json_helpers")`
4. Which runs `init_json_helpers()` factory
5. All services in the chain are now initialized

## Cycle Detection

Uses "initializing" flag per service, matching LazyStatus.Evaluating from `lazy_val.spl`:
1. Before calling factory: set `_di_initializing[name] = true`
2. If re-entered while initializing: panic with "Circular dependency: {name}"
3. After factory completes: set `_di_initializing[name] = false`

## Architecture

```
config/di.sdn                          -- Profile + service definitions
src/compiler/di_runtime.spl             -- Core lazy DI engine
src/compiler/di_config.spl              -- SDN config loader
src/app/mcp/services.spl                -- Service trait interfaces
src/app/desugar/lazy_proxy_gen.spl      -- Auto-proxy code generator
src/app/desugar/mod.spl                 -- Pipeline integration
src/app/mcp/main.spl                    -- Migration target
```

## Performance Expectations

- **Prod profile**: 30-50% reduction in time-to-first-response
- **Dev/test profiles**: No change (eager, same as current)
- **Memory**: Minimal overhead (one Dict per service registry, small proxy structs)
- **Runtime cost per lazy call**: One Dict lookup + nil check (negligible after first call)

## Key Design Decisions

| Decision | Choice | Rationale |
|----------|--------|-----------|
| Proxy implementation | Text-level desugar pass | Works within interpreter constraints |
| Mutable state | Module-level Dict | Closures can't modify captured vars |
| Cycle detection | "initializing" flag | Matches lazy_val.spl pattern |
| Profile resolution | SDN config | Flexible per-service override |
| Cascade trigger | Named delegation fns | No lambda capture issues |
| No new value type | Proxy = regular struct | Avoids modifying eval.spl |

## Related Files

- `src/lib/nogc_sync_mut/lazy_val.spl` -- LazyStatus enum, cycle detection reference
- `src/compiler/di.spl` -- Existing DI container (complementary, not replaced)
- `src/app/desugar/trait_scanner.spl` -- Trait scanning (reused for proxy gen)
- `src/app/desugar/trait_desugar.spl` -- Trait-to-struct pattern reference
- `src/app/desugar/forwarding.spl` -- Delegation code gen pattern
- `src/lib/common/sdn/` -- SDN parser for config loading
