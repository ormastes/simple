# BackendPort Typed Composition Root

**Feature ID:** #BACKEND-001 | **Category:** Compiler | **Status:** Active

_Source: `test/feature/app/backend_port_feature_spec.spl`_

---

## Overview

Tests the BackendPort typed composition root that replaces string-keyed DI with a typed struct
on CompileContext. Covers four phases: struct shape validation (name, run_fn, supports_jit_fn,
target_triple_fn fields), factory creation for noop and custom backends, integration with
CompilerServices ensuring the backend field is wired correctly alongside other ports, and type
safety including name uniqueness and backend identification via target triple.

## Syntax

```simple
val services = create_default_services()
val backend = services.backend
expect(backend.name).to_equal("noop-backend")

val f = backend.supports_jit_fn
val result = f()
expect(result).to_equal(false)
```

---

## Test Summary

| Metric | Count |
|--------|-------|
| Tests | 35 |

## Test Structure

### BackendPort Feature: Phase 1 - Struct shape

#### name field

- ✅ BackendPort has name field
- ✅ name field is a non-empty text
#### compile function field

- ✅ BackendPort has run_fn field
- ✅ run_fn is a callable function
#### emit function fields

- ✅ BackendPort has supports_jit_fn field
- ✅ BackendPort has target_triple_fn field
- ✅ supports_jit_fn is callable and returns bool
- ✅ target_triple_fn is callable and returns text
### BackendPort Feature: Phase 2 - Factory creation

#### noop backend factory

- ✅ noop backend has correct name
- ✅ noop backend compile fn returns result
- ✅ noop backend supports_jit_fn returns false
- ✅ noop backend target_triple_fn returns noop
#### custom backend creation

- ✅ custom backend can define its own supports_jit behavior
- ✅ custom backend can define its own target_triple
- ✅ custom backend target triple differs from noop triple
#### multiple backends

- ✅ two noop backends have same name
- ✅ two noop backends have same target triple
### BackendPort Feature: Phase 3 - Integration with CompilerServices

#### CompilerServices has backend field

- ✅ CompilerServices.backend is a BackendPort
- ✅ backend field is distinct from lexer field
- ✅ backend field is distinct from parser field
- ✅ backend field is distinct from logger field
#### backend swapping in services

- ✅ backend can be replaced with different name via delegation
- ✅ alternate backend target triple is different from noop
#### backend port functions callable end-to-end

- ✅ full chain: services -> backend -> supports_jit
- ✅ full chain: services -> backend -> target_triple
- ✅ full chain: services -> backend -> name then supports_jit
### BackendPort Feature: Phase 4 - Type safety

#### name is unique identifier

- ✅ BackendPort name is meaningful (not empty)
- ✅ noop backend name starts with noop prefix
- ✅ noop backend name contains backend suffix
#### different backends have different names

- ✅ noop backend name differs from custom name
- ✅ noop backend name differs from wasm backend name
- ✅ backend identification works via target_triple
#### fn-field type correctness

- ✅ supports_jit_fn always returns a bool
- ✅ target_triple_fn always returns a text
- ✅ calling fn-fields multiple times is idempotent

