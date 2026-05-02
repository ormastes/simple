# Publish Specification

## At a Glance

| Field | Value |
|-------|-------|
| Source | `test/feature/app/publish_spec.spl` |
| Updated | 2026-04-07 |
| Generator | `simple sspec-docgen` (Rust) |

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 10 |
| Active scenarios | 10 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |

## Overview

Documentation was generated from executable SSpec scenarios.

## Evidence

| Category | Count |
|----------|------:|
| Artifacts | 1 |

### Artifacts

| Item | Kind | Path |
|------|------|------|
| `result.json` | JSON artifact | `build/test-artifacts/feature/app/publish/result.json` |

## Scenarios

- parses package name from manifest
- parses package version from manifest
- returns error when no simple.sdn exists
- does not push to GHCR in dry-run mode
- excludes .jj directory
- excludes target directory
- excludes .env files
- includes simple.sdn manifest
- includes src directory
- computes sha256 checksum with prefix
