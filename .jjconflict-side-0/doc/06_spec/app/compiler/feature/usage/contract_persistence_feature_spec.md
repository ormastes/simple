# Contract Persistence - File I/O

Tests consumer-driven contract persistence including serialization to Pact-compatible JSON format, saving contracts to the filesystem, and mock Pact broker integration for contract publishing. Verifies the full contract lifecycle from creation through builder pattern to file output.

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #TEST-001 |
| Category | Infrastructure |
| Status | Active |
| Source | `test/feature/usage/contract_persistence_feature_spec.spl` |
| Updated | 2026-04-07 |
| Generator | `simple sspec-docgen` (Rust) |

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 6 |
| Active scenarios | 6 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |

## Overview

Tests consumer-driven contract persistence including serialization to
Pact-compatible JSON format, saving contracts to the filesystem, and
mock Pact broker integration for contract publishing. Verifies the full
contract lifecycle from creation through builder pattern to file output.

## Syntax

```simple
val contract = ct.Contract__new("web-app", "user-api")
val json = contract.to_pact_json()
val result = contract.save("/tmp/contract-test.json")
```
Contract Persistence Feature Spec

Feature: Save contracts to files for later verification
Implements Pact-compatible contract persistence

## Evidence

| Category | Count |
|----------|------:|
| Artifacts | 1 |

### Artifacts

| Item | Kind | Path |
|------|------|------|
| `result.json` | JSON artifact | `build/test-artifacts/feature/usage/contract_persistence_feature/result.json` |

## Scenarios

- converts contract to valid JSON
- includes all interaction details in JSON
- saves contract to file
- returns error when save fails
- enables contracts for broker publishing
- demonstrates saving contracts
