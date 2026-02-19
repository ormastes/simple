# DI Lock Feature

**Feature ID:** #DI-004 | **Category:** Compiler | **Status:** Active

_Source: `test/feature/usage/di_lock_feature_spec.spl`_

---

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

---

## Test Summary

| Metric | Count |
|--------|-------|
| Tests | 29 |

## Test Structure

### DI Lock Feature: Phase 1 - Lock state

- ✅ starts unlocked
- ✅ lock() transitions to locked state
- ✅ is_locked() returns true after lock
- ✅ unlock() transitions back to unlocked
- ✅ is_locked() returns false after unlock
- ✅ is_locked() returns false on fresh container
### DI Lock Feature: Phase 2 - Locked behavior

- ✅ locked container rejects bind_instance
- ✅ locked container rejects bind
- ✅ locked container still allows resolve
- ✅ locked container still allows resolve_or
- ✅ locked container still allows has check
- ✅ locked container resolve_or returns default for missing
- ✅ locked container rejects bind_tagged
### DI Lock Feature: Phase 3 - Lock semantics

- ✅ can lock and unlock multiple times
- ✅ bindings before lock are preserved after lock
- ✅ unlock allows new bindings again
- ✅ pre-lock binding not overwritten when locked
- ✅ locked state does not affect resolve_or nil default
### DI Lock Feature: Phase 4 - Integration

- ✅ container locked after setup phase
- ✅ runtime resolution works on locked container
- ✅ locked container with resolve_singleton works
- ✅ multiple services still resolvable after lock
- ✅ env-var lock blocks bind_instance
- ✅ env-var di_test bypass allows bind_instance
### DI Lock Feature: Phase 5 - System test

- ✅ full registration-lock-resolve cycle works
- ✅ complete lifecycle: register, lock, reject, unlock, register again
- ✅ factory bindings registered before lock resolve correctly
- ✅ di_is_system_test_locked returns false with no env vars
- ✅ di_is_system_test_locked returns true with SIMPLE_SYSTEM_TEST=1

