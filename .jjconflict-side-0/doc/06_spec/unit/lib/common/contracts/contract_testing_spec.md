# Contract Testing Specification

*Source: `test/unit/lib/common/contracts/contract_testing_spec.spl`*
*Last Updated: 2026-05-28*

---

## Overview

Manual mirrored SPipe documentation for the Pact-style contract testing helper
coverage in `src/lib/common/contract.spl`.

## Evidence

### Artifacts

- test/unit/lib/common/contracts/contract/summary.txt

## Test Summary

| Metric | Count |
|--------|-------|
| Scenarios | 22 |
| Failed | 0 |
| Skipped | 0 |

## Scenarios

- creates contract for consumer and provider
- defines provider state
- defines interaction
- builds GET request
- builds POST request with body
- adds request headers
- builds response with status
- builds response with body
- adds response headers
- like() matches type not value
- term() matches regex pattern
- each_like() matches array structure
- saves contract to JSON file
- generates Pact-compatible JSON
- creates mock server from contract
- mock server responds to requests
- verifies all interactions matched
- verifies provider against contract
- sets up provider states
- publishes contract to broker
- fetches contracts from broker
- counts contracts in broker
