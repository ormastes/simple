# Di Extensions Feature Specification

## At a Glance

| Field | Value |
|-------|-------|
| Source | `test/feature/usage/di_extensions_feature_spec.spl` |
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

Documentation was generated from executable SSpec scenarios.

## Evidence

| Category | Count |
|----------|------:|
| Artifacts | 1 |

### Artifacts

| Item | Kind | Path |
|------|------|------|
| `result.json` | JSON artifact | `target/test-artifacts/feature/usage/di_extensions_feature/result.json` |

## Scenarios

- can register a plugin by name
- can retrieve a registered plugin
- unregistered plugin returns nil via resolve_or
- unregistered plugin returns default via resolve_or
- has returns false for unregistered plugin
- has returns true after registration
- can register integer plugin value
- can register boolean plugin value
- can register multiple independent plugins
- plugins do not interfere with each other
- can overwrite an existing plugin registration
- resolves three plugins independently
- factory and instance bindings coexist
- resolves two plugins after separate registration
- extensions container starts empty
- extensions container is independent of typed backend port
- core services not accessible via extensions
- factory-bound extension resolves lazily
- profile is preserved on extensions container
- extensions container starts with empty bindings
- register_extension adds to extensions (via bind_instance)
- get_extension retrieves registered value (via resolve_or)
- get_extension returns nil for unregistered (resolve_or nil default)
- extensions uses profile from options
- extensions starts unlocked
- plugin registration before lock succeeds
- plugin retrieval after lock works
- plugin registration after lock fails or is ignored
- unlock allows plugin registration again
- full plugin lifecycle: register, lock, resolve, unlock, re-register
- locked container uses resolve_or for missing plugins
