# Contract Persistence - File I/O

**Feature ID:** #TEST-001 | **Category:** Infrastructure | **Status:** Active

_Source: `test/feature/usage/contract_persistence_feature_spec.spl`_

---

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

---

## Test Summary

| Metric | Count |
|--------|-------|
| Tests | 6 |

## Test Structure

### Feature #2401: Contract Persistence - File I/O

#### Contract serialization

- ✅ converts contract to valid JSON
- ✅ includes all interaction details in JSON
#### Contract file persistence

- ✅ saves contract to file
- ✅ returns error when save fails
#### Pact broker integration

- ✅ enables contracts for broker publishing
#### Usage examples

- ✅ demonstrates saving contracts

