# Registry Search Specification

**Feature ID:** #959-960 | **Category:** Tooling | **Difficulty:** 2/5 | **Status:** In Progress

_Source: `test/feature/app/search_spec.spl`_

---

## Overview
Tests for the `simple search` command that queries the package listing.

## Key Concepts
- Package listing parsing
- Name and description matching
- Result limiting

---

## Test Summary

| Metric | Count |
|--------|-------|
| Tests | 5 |

## Test Structure

### Search Command

#### when packages match

- ✅ finds packages by name
- ✅ finds packages by description
- ✅ is case insensitive
#### when no packages match

- ✅ returns empty list
#### when limit is applied

- ✅ respects result limit

