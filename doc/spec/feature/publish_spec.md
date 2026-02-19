# Registry Publish Specification

**Feature ID:** #950-952 | **Category:** Tooling | **Difficulty:** 3/5 | **Status:** In Progress

_Source: `test/feature/app/publish_spec.spl`_

---

## Overview
Tests for the `simple publish` command that builds .spk tarballs
and pushes them to GHCR.

## Key Concepts
- Package manifest validation
- .spk tarball creation
- Checksum computation
- GHCR push via oras

---

## Test Summary

| Metric | Count |
|--------|-------|
| Tests | 10 |

## Test Structure

### Publish Command

#### when manifest is valid

- ✅ parses package name from manifest
- ✅ parses package version from manifest
#### when manifest is missing

- ✅ returns error when no simple.sdn exists
#### when using --dry-run

- ✅ does not push to GHCR in dry-run mode
### SPK Tarball

#### when building tarball

- ✅ excludes .jj directory
- ✅ excludes target directory
- ✅ excludes .env files
- ✅ includes simple.sdn manifest
- ✅ includes src directory
### Checksum

- ✅ computes sha256 checksum with prefix

