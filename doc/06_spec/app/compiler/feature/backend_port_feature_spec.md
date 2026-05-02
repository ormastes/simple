# Backend Port Feature Specification

## At a Glance

| Field | Value |
|-------|-------|
| Source | `test/feature/app/backend_port_feature_spec.spl` |
| Updated | 2026-04-07 |
| Generator | `simple sspec-docgen` (Rust) |

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 35 |
| Active scenarios | 35 |
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
| `result.json` | JSON artifact | `build/test-artifacts/feature/app/backend_port_feature/result.json` |

## Scenarios

- BackendPort has name field
- name field is a non-empty text
- BackendPort has run_fn field
- run_fn is a callable function
- BackendPort has supports_jit_fn field
- BackendPort has target_triple_fn field
- supports_jit_fn is callable and returns bool
- target_triple_fn is callable and returns text
- noop backend has correct name
- noop backend compile fn returns result
- noop backend supports_jit_fn returns false
- noop backend target_triple_fn returns noop
- custom backend can define its own supports_jit behavior
- custom backend can define its own target_triple
- custom backend target triple differs from noop triple
- two noop backends have same name
- two noop backends have same target triple
- CompilerServices.backend is a BackendPort
- backend field is distinct from lexer field
- backend field is distinct from parser field
- backend field is distinct from logger field
- backend can be replaced with different name via delegation
- alternate backend target triple is different from noop
- full chain: services -> backend -> supports_jit
- full chain: services -> backend -> target_triple
- full chain: services -> backend -> name then supports_jit
- BackendPort name is meaningful (not empty)
- noop backend name starts with noop prefix
- noop backend name contains backend suffix
- noop backend name differs from custom name
- noop backend name differs from wasm backend name
- backend identification works via target_triple
- supports_jit_fn always returns a bool
- target_triple_fn always returns a text
- calling fn-fields multiple times is idempotent
