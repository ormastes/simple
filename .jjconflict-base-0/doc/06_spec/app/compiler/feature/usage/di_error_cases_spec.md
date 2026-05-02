# DI Error Cases

Tests the failure paths and edge cases of the DiContainer dependency injection system. Covers locked container behavior (binding rejection), missing key fallback via resolve_or, edge cases like empty keys and key overwrites, resolve behavior through locks, and environment variable-based system test locking via SIMPLE_SYSTEM_TEST/SIMPLE_DI_TEST.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | In Progress |
| Source | `test/feature/usage/di_error_cases_spec.spl` |
| Updated | 2026-04-07 |
| Generator | `simple sspec-docgen` (Rust) |

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 22 |
| Active scenarios | 22 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |

## Overview

Tests the failure paths and edge cases of the DiContainer dependency injection system.
Covers locked container behavior (binding rejection), missing key fallback via resolve_or,
edge cases like empty keys and key overwrites, resolve behavior through locks, and
environment variable-based system test locking via SIMPLE_SYSTEM_TEST/SIMPLE_DI_TEST.

## Evidence

| Category | Count |
|----------|------:|
| Artifacts | 1 |

### Artifacts

| Item | Kind | Path |
|------|------|------|
| `result.json` | JSON artifact | `build/test-artifacts/feature/usage/di_error_cases/result.json` |

## Scenarios

- bind_instance on locked container does not store value
- bind factory on locked container does not register
- bind_for_profile on locked container does not register
- locked container does not overwrite previously bound value
- is_locked returns true after explicit lock
- is_locked returns false after unlock
- resolve_or returns default text for missing key
- resolve_or returns default integer for missing key
- has returns false for missing key
- resolve_or returns bound value when key exists
- has returns true after bind_instance
- empty string key can be stored and retrieved
- overwriting key keeps the latest value
- multiple distinct keys are independent
- singleton is resolved from singletons not bindings
- factory binding is callable after bind
- resolve_or for existing key works when locked
- resolve_or for missing key returns default when locked
- resolve for pre-lock binding works after lock
- bind rejected when SIMPLE_SYSTEM_TEST=1 and SIMPLE_DI_TEST not set
- bind allowed when SIMPLE_DI_TEST=1 bypasses env lock
- di_is_system_test_locked returns false when env not set
