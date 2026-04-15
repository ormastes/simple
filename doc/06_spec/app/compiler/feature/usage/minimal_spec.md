# Minimal Test Spec

A minimal smoke test that verifies the test runner can load a spec file with a basic describe/it block and execute a trivial assertion. Used as a baseline sanity check for the SSpec framework and test infrastructure.

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #TEST-002 |
| Category | Infrastructure |
| Status | Active |
| Source | `test/feature/usage/minimal_spec.spl` |
| Updated | 2026-04-07 |
| Generator | `simple sspec-docgen` (Rust) |

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 2 |
| Active scenarios | 2 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |

## Overview

A minimal smoke test that verifies the test runner can load a spec file
with a basic describe/it block and execute a trivial assertion. Used as a
baseline sanity check for the SSpec framework and test infrastructure.

## Syntax

```simple
describe "Test":
it "works":
check(true)
```

## Evidence

| Category | Count |
|----------|------:|
| Artifacts | 1 |

### Artifacts

| Item | Kind | Path |
|------|------|------|
| `result.json` | JSON artifact | `target/test-artifacts/feature/usage/minimal/result.json` |

## Scenarios

- works
- works
