# Registry Index Specification

Tests for the sparse package index: parsing SDN entries, computing index paths, and searching.

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #956-958 |
| Category | Tooling |
| Difficulty | 2/5 |
| Status | In Progress |
| Source | `test/feature/usage/index_spec.spl` |
| Updated | 2026-04-07 |
| Generator | `simple sspec-docgen` (Rust) |

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 16 |
| Active scenarios | 16 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |

## Overview
Tests for the sparse package index: parsing SDN entries,
computing index paths, and searching.

## Key Concepts
- SDN index entry parsing
- Sparse directory path computation
- Package listing and search

## Evidence

| Category | Count |
|----------|------:|
| Artifacts | 1 |

### Artifacts

| Item | Kind | Path |
|------|------|------|
| `result.json` | JSON artifact | `build/test-artifacts/feature/usage/index/result.json` |

## Scenarios

- computes path for 4+ char names
- computes path for long names
- computes path for 3 char names
- computes path for 2 char names
- computes path for 1 char names
- parses package name
- parses package description
- parses version entries
- parses version checksum
- parses yanked flag
- parses dependencies
- parses dependency constraint
- finds latest non-yanked version
- finds dependencies for a version
- finds specific version entry
- returns empty for missing version
