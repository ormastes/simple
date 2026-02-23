# Registry Install Specification

**Feature ID:** #953-955 | **Category:** Tooling | **Difficulty:** 3/5 | **Status:** In Progress

_Source: `test/feature/app/install_spec.spl`_

---

## Overview
Tests for installing packages from the GHCR-based registry.

## Key Concepts
- Index lookup and version resolution
- OCI artifact pull
- Checksum verification
- Local package extraction

---

## Test Summary

| Metric | Count |
|--------|-------|
| Tests | 11 |

## Test Structure

### Install from Registry

#### when package exists

- ✅ resolves latest non-yanked version
- ✅ pulls artifact from GHCR
- ✅ verifies checksum after download
- ✅ extracts to packages directory
#### when package not found

- ✅ shows error message
#### when version is yanked

- ✅ shows warning for yanked version
- ✅ selects next available version
#### when using --save flag

- ✅ adds package to simple.sdn dependencies
### Version Resolution

- ✅ selects latest version when no constraint
- ✅ respects caret constraint
- ✅ respects exact version constraint

