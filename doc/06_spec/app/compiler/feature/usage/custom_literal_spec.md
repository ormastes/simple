# Custom Literal Syntax

Tests the custom collection literal syntax, specifically the `s{...}` prefix for set literals. Verifies that set literals are distinguished from ordinary identifiers and blocks, handles nested set literals with correct depth tracking, and rejects malformed custom literal expressions.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Language Features |
| Status | In Progress |
| Source | `test/feature/usage/custom_literal_spec.spl` |
| Updated | 2026-04-07 |
| Generator | `simple sspec-docgen` (Rust) |

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 3 |
| Active scenarios | 3 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |

## Overview

Tests the custom collection literal syntax, specifically the `s{...}` prefix for set
literals. Verifies that set literals are distinguished from ordinary identifiers and
blocks, handles nested set literals with correct depth tracking, and rejects malformed
custom literal expressions.

## Evidence

| Category | Count |
|----------|------:|
| Artifacts | 1 |

### Artifacts

| Item | Kind | Path |
|------|------|------|
| `result.json` | JSON artifact | `target/test-artifacts/feature/usage/custom_literal/result.json` |

## Scenarios

- distinguishes set literals from variables
- handles nested set literals
- rejects malformed custom literals
