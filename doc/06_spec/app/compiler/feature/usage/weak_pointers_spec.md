# Weak Pointers Specification

Weak references provide non-owning references to values managed by a global weak reference table. When the target is invalidated (or strong count drops to zero), weak references return -1 on upgrade.

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #PTR-WEAK |
| Category | Runtime |
| Status | Implemented |
| Source | `test/feature/usage/weak_pointers_spec.spl` |
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

Weak references provide non-owning references to values managed by a global
weak reference table. When the target is invalidated (or strong count drops
to zero), weak references return -1 on upgrade.

## Evidence

| Category | Count |
|----------|------:|
| Artifacts | 1 |

### Artifacts

| Item | Kind | Path |
|------|------|------|
| `result.json` | JSON artifact | `build/test-artifacts/feature/usage/weak_pointers/result.json` |

## Scenarios

- creates and upgrades weak reference
- returns -1 after invalidation
- invalidates when strong count drops to zero
- both expire together
- tracks add and remove
