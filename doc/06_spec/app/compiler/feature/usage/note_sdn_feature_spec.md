# SMF note.sdn Instantiation Tracking

Tests the note.sdn section in SMF (Simple Module Format) for tracking generic instantiation metadata. The feature enables tracking which generic types and functions have been instantiated during compilation.

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #GENERIC-002 |
| Category | Compiler |
| Status | In Progress |
| Source | `test/feature/usage/note_sdn_feature_spec.spl` |
| Updated | 2026-04-07 |
| Generator | `simple sspec-docgen` (Rust) |

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 1 |
| Active scenarios | 1 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |

## Overview

Tests the note.sdn section in SMF (Simple Module Format) for tracking generic
instantiation metadata. The feature enables tracking which generic
types and functions have been instantiated during compilation.

## Syntax

```simple
```

## Evidence

| Category | Count |
|----------|------:|
| Artifacts | 1 |

### Artifacts

| Item | Kind | Path |
|------|------|------|
| `result.json` | JSON artifact | `target/test-artifacts/feature/usage/note_sdn_feature/result.json` |

## Scenarios

- tracks generic instantiation metadata
