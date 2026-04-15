# DI System Test Lock - All Phases

Comprehensive phase tests for the DI system test lock feature covering all five phases: lock state transitions (lock/unlock/cycle), binding rejection when locked (bind_instance, bind, bind_tagged), resolution behavior while locked (resolve, resolve_or, has), lock integration with registration protection, and full DI lifecycle including environment variable lock with SIMPLE_DI_TEST bypass.

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #DI-003 |
| Category | Compiler |
| Status | Active |
| Source | `test/feature/usage/di_lock_all_phases_spec.spl` |
| Updated | 2026-04-07 |
| Generator | `simple sspec-docgen` (Rust) |

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 31 |
| Active scenarios | 31 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |

## Overview

Comprehensive phase tests for the DI system test lock feature covering all five
phases: lock state transitions (lock/unlock/cycle), binding rejection when locked
(bind_instance, bind, bind_tagged), resolution behavior while locked (resolve,
resolve_or, has), lock integration with registration protection, and full DI
lifecycle including environment variable lock with SIMPLE_DI_TEST bypass.

## Syntax

```simple
val di = DiContainer(bindings: {}, singletons: {}, profile: "dev", all_bindings: [], locked: false)
di.lock()
di.bind_instance("key", "value")  # silently rejected
expect(di.resolve_or("key", "fallback")).to_equal("fallback")
```
DI Lock All Phases Spec

Comprehensive phase tests for Feature 9: DI System Test Lock.
Covers all 5 phases of the DI lock feature lifecycle.

Feature: DI System Test Lock (Feature 9)
Source: src/compiler/di.spl

DiContainer has:
  lock()           - explicitly lock (prevents all bind operations)
  unlock()         - explicitly unlock (does NOT override env-var lock)
  is_locked()      - true if locked field OR env-var lock is active
  bind_instance()  - bind a pre-created instance (rejected when locked)
  bind()           - bind a factory fn (rejected when locked)
  bind_for_profile() - bind factory for a specific profile (rejected when locked)
  bind_tagged()    - bind with tags (rejected when locked)
  resolve()        - resolve binding by name (always works)
  resolve_or()     - resolve with default fallback (always works)
  has()            - check if binding exists (always works)

## Evidence

| Category | Count |
|----------|------:|
| Artifacts | 1 |

### Artifacts

| Item | Kind | Path |
|------|------|------|
| `result.json` | JSON artifact | `target/test-artifacts/feature/usage/di_lock_all_phases/result.json` |

## Scenarios

- new container is unlocked
- locked field is false on construction
- binding works before any lock
- lock sets is_locked to true
- unlock after lock sets is_locked to false
- multiple lock calls remain locked
- unlock without prior lock stays unlocked
- lock-unlock-lock cycle ends locked
- bind_instance rejected when locked
- bind_instance succeeds before lock
- bind factory rejected when locked
- bind_tagged rejected when locked
- bind_instance works after unlock
- bind factory works after unlock
- resolve pre-lock singleton works
- resolve pre-lock factory works
- resolve_or returns registered value when locked
- resolve_or returns default for missing when locked
- has returns true for pre-lock binding
- has returns false for post-lock rejected binding
- pre-lock binding cannot be overwritten while locked
- multiple pre-lock bindings all resolvable after lock
- new bindings added after unlock are accessible
- lock-unlock-relock preserves all accumulated bindings
- di_is_system_test_locked returns false normally
- env lock is active when system test active
- full DI lifecycle: register, lock, resolve, unlock, extend
- resolve_or covers missing services during operation
- has correctly reflects what is and is not registered
- env lock reflects env state then resets
- SIMPLE_DI_TEST=1 bypass disables env lock
