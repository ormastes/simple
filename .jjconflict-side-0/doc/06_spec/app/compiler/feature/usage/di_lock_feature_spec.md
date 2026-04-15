# DI Lock Feature

Tests the DiContainer lock/unlock mechanism across all phases: lock state transitions, locked behavior that rejects new bindings while allowing resolution, lock semantics including pre-lock binding preservation and overwrite protection, integration with environment variable locking, and a complete system test covering the full registration-lock-resolve-unlock-extend lifecycle.

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #DI-004 |
| Category | Compiler |
| Status | Active |
| Source | `test/feature/usage/di_lock_feature_spec.spl` |
| Updated | 2026-04-07 |
| Generator | `simple sspec-docgen` (Rust) |

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 29 |
| Active scenarios | 29 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |

## Overview

Tests the DiContainer lock/unlock mechanism across all phases: lock state
transitions, locked behavior that rejects new bindings while allowing resolution,
lock semantics including pre-lock binding preservation and overwrite protection,
integration with environment variable locking, and a complete system test
covering the full registration-lock-resolve-unlock-extend lifecycle.

## Syntax

```simple
val di = DiContainer(bindings: {}, singletons: {}, profile: "dev", all_bindings: [], locked: false)
di.bind_instance("Backend", "production-backend")
di.lock()
expect(di.resolve("Backend")).to_equal("production-backend")
```
DI Lock Feature Spec

Feature 9: DI Lock

DiContainer with lock()/unlock() — once locked, no new bindings can be added.
Covers all phases: lock state, locked behavior, lock semantics, integration,
and full system test.

## Evidence

| Category | Count |
|----------|------:|
| Artifacts | 1 |

### Artifacts

| Item | Kind | Path |
|------|------|------|
| `result.json` | JSON artifact | `target/test-artifacts/feature/usage/di_lock_feature/result.json` |

## Scenarios

- starts unlocked
- lock() transitions to locked state
- is_locked() returns true after lock
- unlock() transitions back to unlocked
- is_locked() returns false after unlock
- is_locked() returns false on fresh container
- locked container rejects bind_instance
- locked container rejects bind
- locked container still allows resolve
- locked container still allows resolve_or
- locked container still allows has check
- locked container resolve_or returns default for missing
- locked container rejects bind_tagged
- can lock and unlock multiple times
- bindings before lock are preserved after lock
- unlock allows new bindings again
- pre-lock binding not overwritten when locked
- locked state does not affect resolve_or nil default
- container locked after setup phase
- runtime resolution works on locked container
- locked container with resolve_singleton works
- multiple services still resolvable after lock
- env-var lock is active when system test active
- env-var di_test bypass disables env lock
- full registration-lock-resolve cycle works
- complete lifecycle: register, lock, reject, unlock, register again
- factory bindings registered before lock resolve correctly
- di_is_system_test_locked returns false with no env vars
- di_is_system_test_locked returns true with SIMPLE_SYSTEM_TEST=1
