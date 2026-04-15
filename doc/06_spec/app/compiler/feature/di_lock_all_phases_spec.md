# DI System Test Lock - All Phases

**Feature ID:** #DI-003 | **Category:** Compiler | **Status:** Active

_Source: `test/feature/usage/di_lock_all_phases_spec.spl`_

---

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

---

## Test Summary

| Metric | Count |
|--------|-------|
| Tests | 31 |

## Test Structure

### DI Lock: Phase 1 - Lock state transitions

#### initial state

- ✅ new container is unlocked
- ✅ locked field is false on construction
- ✅ binding works before any lock
#### lock transitions

- ✅ lock sets is_locked to true
- ✅ unlock after lock sets is_locked to false
- ✅ multiple lock calls remain locked
- ✅ unlock without prior lock stays unlocked
- ✅ lock-unlock-lock cycle ends locked
### DI Lock: Phase 2 - Binding behavior when locked

#### bind_instance is blocked

- ✅ bind_instance rejected when locked
- ✅ bind_instance succeeds before lock
#### bind factory is blocked

- ✅ bind factory rejected when locked
- ✅ bind_tagged rejected when locked
#### bind allowed after unlock

- ✅ bind_instance works after unlock
- ✅ bind factory works after unlock
### DI Lock: Phase 3 - Resolution behavior

#### resolve works while locked

- ✅ resolve pre-lock singleton works
- ✅ resolve pre-lock factory works
#### resolve_or works while locked

- ✅ resolve_or returns registered value when locked
- ✅ resolve_or returns default for missing when locked
#### has works correctly

- ✅ has returns true for pre-lock binding
- ✅ has returns false for post-lock rejected binding
### DI Lock: Phase 4 - Lock integration with registration

#### protects production bindings

- ✅ pre-lock binding cannot be overwritten while locked
- ✅ multiple pre-lock bindings all resolvable after lock
#### extend after unlock

- ✅ new bindings added after unlock are accessible
- ✅ lock-unlock-relock preserves all accumulated bindings
#### env-var lock mechanism

- ✅ di_is_system_test_locked returns false normally
- ✅ env lock blocks bind_instance when system test active
### DI Lock: Phase 5 - System full DI lifecycle

#### complete register-lock-resolve cycle

- ✅ full DI lifecycle: register, lock, resolve, unlock, extend
- ✅ resolve_or covers missing services during operation
- ✅ has correctly reflects what is and is not registered
#### env-var lock full flow

- ✅ env lock is_locked reflects env state then resets
- ✅ SIMPLE_DI_TEST=1 bypass allows registration in env-locked state

