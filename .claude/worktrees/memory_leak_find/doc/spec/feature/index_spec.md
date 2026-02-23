# Registry Index Specification

**Feature ID:** #956-958 | **Category:** Tooling | **Difficulty:** 2/5 | **Status:** In Progress

_Source: `test/feature/usage/index_spec.spl`_

---

## Overview
Tests for the sparse package index: parsing SDN entries,
computing index paths, and searching.

## Key Concepts
- SDN index entry parsing
- Sparse directory path computation
- Package listing and search

---

## Test Summary

| Metric | Count |
|--------|-------|
| Tests | 16 |

## Test Structure

### Index Path Computation

- ✅ computes path for 4+ char names
- ✅ computes path for long names
- ✅ computes path for 3 char names
- ✅ computes path for 2 char names
- ✅ computes path for 1 char names
### Index Entry Parsing

- ✅ parses package name
- ✅ parses package description
- ✅ parses version entries
- ✅ parses version checksum
- ✅ parses yanked flag
- ✅ parses dependencies
- ✅ parses dependency constraint
### Index Queries

- ✅ finds latest non-yanked version
- ✅ finds dependencies for a version
- ✅ finds specific version entry
- ✅ returns empty for missing version

