# DI Container Error Cases

**Feature ID:** #DI-001 | **Category:** Compiler | **Status:** Active

_Source: `test/feature/usage/di_error_cases_spec.spl`_

---

## Overview

Tests failure paths and edge cases of the DiContainer including locked container
behavior (silently rejecting bind operations), missing key resolution with
fallback defaults, empty and overwritten key handling, and environment variable
based system test locking with SIMPLE_SYSTEM_TEST and SIMPLE_DI_TEST bypass.

## Syntax

```simple
val di = DiContainer(bindings: {}, singletons: {}, profile: "dev", all_bindings: [], locked: false)
di.bind_instance("key", "value")
di.lock()
val result = di.resolve_or("missing_key", "default_val")
```

---

## Test Summary

| Metric | Count |
|--------|-------|
| Tests | 22 |

## Test Structure

### DI Error Cases: locked container rejects bindings

- ✅ bind_instance on locked container does not store value
- ✅ bind factory on locked container does not register
- ✅ bind_for_profile on locked container does not register
- ✅ locked container does not overwrite previously bound value
- ✅ is_locked returns true after explicit lock
- ✅ is_locked returns false after unlock
### DI Error Cases: missing key fallback

- ✅ resolve_or returns default text for missing key
- ✅ resolve_or returns default integer for missing key
- ✅ has returns false for missing key
- ✅ resolve_or returns bound value when key exists
- ✅ has returns true after bind_instance
### DI Error Cases: edge cases

- ✅ empty string key can be stored and retrieved
- ✅ overwriting key keeps the latest value
- ✅ multiple distinct keys are independent
- ✅ singleton is resolved from singletons not bindings
- ✅ factory binding is callable after bind
### DI Error Cases: resolve works through lock

- ✅ resolve_or for existing key works when locked
- ✅ resolve_or for missing key returns default when locked
- ✅ resolve for pre-lock binding works after lock
### DI Error Cases: env-var lock rejects bindings

- ✅ bind rejected when SIMPLE_SYSTEM_TEST=1 and SIMPLE_DI_TEST not set
- ✅ bind allowed when SIMPLE_DI_TEST=1 bypasses env lock
- ✅ di_is_system_test_locked returns false when env not set

