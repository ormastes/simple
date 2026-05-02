# Btree Basic Specification

BTreeMap Basic Operations System Test

## At a Glance

| Field | Value |
|-------|-------|
| Category | System/Collections |
| Status | Active |
| Source | `test/feature/usage/btree_basic_spec.spl` |
| Updated | 2026-04-07 |
| Generator | `simple sspec-docgen` (Rust) |

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 7 |
| Active scenarios | 7 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |

BTreeMap Basic Operations System Test

**Feature:** Collections.BTreeMap
## Description

Integration tests for BTreeMap (ordered map) basic operations through the FFI layer.

Tests cover:
- Map creation and initialization
- Key-value insertion and retrieval
- Key ordering maintenance
- Key existence checking and removal
- Collection mutations (clear)
- Array/collection views (keys, values)

**Integration Scope:** BTreeMap + Collections FFI
**Complexity:** Low
**Coverage Impact:** btreemap.rs (0%→40%), collections FFI

## Evidence

| Category | Count |
|----------|------:|
| Artifacts | 1 |

### Artifacts

| Item | Kind | Path |
|------|------|------|
| `result.json` | JSON artifact | `build/test-artifacts/feature/usage/btree_basic/result.json` |

## Scenarios

- creates new BTreeMap
- inserts and retrieves values
- maintains sorted order
- checks if key exists
- removes keys
- clears all entries
- gets all values
