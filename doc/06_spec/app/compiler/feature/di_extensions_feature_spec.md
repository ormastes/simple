# DI Extension Container

**Feature ID:** #DI-002 | **Category:** Compiler | **Status:** Active

_Source: `test/feature/usage/di_extensions_feature_spec.spl`_

---

## Overview

Tests the DiContainer as a dynamic plugin/extension registration point separate
from typed core services. Covers all five phases: basic plugin registration and
retrieval, multiple independent plugins, separation from core services,
integration with CompileContext, and plugin lifecycle with lock/unlock semantics.

## Syntax

```simple
val ext = DiContainer(bindings: {}, singletons: {}, profile: "dev", all_bindings: [], locked: false)
ext.bind_instance("Profiler", "profiler-v1")
val result = ext.resolve_or("MissingPlugin", "default-value")
```

---

## Test Summary

| Metric | Count |
|--------|-------|
| Tests | 31 |

## Test Structure

### DI Extensions Feature: Phase 1 - Basic plugin registration

- ✅ can register a plugin by name
- ✅ can retrieve a registered plugin
- ✅ unregistered plugin returns nil via resolve_or
- ✅ unregistered plugin returns default via resolve_or
- ✅ has returns false for unregistered plugin
- ✅ has returns true after registration
- ✅ can register integer plugin value
- ✅ can register boolean plugin value
### DI Extensions Feature: Phase 2 - Multiple plugins

- ✅ can register multiple independent plugins
- ✅ plugins do not interfere with each other
- ✅ can overwrite an existing plugin registration
- ✅ resolves three plugins independently
- ✅ factory and instance bindings coexist
- ✅ resolves two plugins after separate registration
### DI Extensions Feature: Phase 3 - Separation from core services

- ✅ extensions container starts empty
- ✅ extensions container is independent of typed backend port
- ✅ core services not accessible via extensions
- ✅ factory-bound extension resolves lazily
- ✅ profile is preserved on extensions container
### DI Extensions Feature: Phase 4 - Integration with CompileContext

- ✅ extensions container starts with empty bindings
- ✅ register_extension adds to extensions (via bind_instance)
- ✅ get_extension retrieves registered value (via resolve_or)
- ✅ get_extension returns nil for unregistered (resolve_or nil default)
- ✅ extensions uses profile from options
- ✅ extensions starts unlocked
### DI Extensions Feature: Phase 5 - Plugin lifecycle

- ✅ plugin registration before lock succeeds
- ✅ plugin retrieval after lock works
- ✅ plugin registration after lock fails or is ignored
- ✅ unlock allows plugin registration again
- ✅ full plugin lifecycle: register, lock, resolve, unlock, re-register
- ✅ locked container uses resolve_or for missing plugins

