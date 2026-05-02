# Unique Pointers Specification

UniquePtr provides exclusive ownership semantics via cooperative move tracking. Since Simple copies on assignment, unique_move returns a new valid ptr and marks the old one as moved internally.

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #PTR-UNIQUE |
| Category | Runtime |
| Status | Implemented |
| Source | `test/feature/usage/unique_pointers_spec.spl` |
| Updated | 2026-04-07 |
| Generator | `simple sspec-docgen` (Rust) |

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 5 |
| Active scenarios | 5 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |

## Overview

UniquePtr provides exclusive ownership semantics via cooperative move tracking.
Since Simple copies on assignment, unique_move returns a new valid ptr and
marks the old one as moved internally.

## Evidence

| Category | Count |
|----------|------:|
| Artifacts | 1 |

### Artifacts

| Item | Kind | Path |
|------|------|------|
| `result.json` | JSON artifact | `build/test-artifacts/feature/usage/unique_pointers/result.json` |

## Scenarios

- creates and reads value
- transfers ownership on move
- get on moved ptr returns -1
- consumes and returns value
- marks as moved
