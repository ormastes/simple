# Native Cache Producer Identity

- Executable: `test/01_unit/compiler/driver/native_cache_producer_identity_spec.spl`
- Requirements: `MBH-REQ-002`, `MBH-REQ-009`
- Evidence class: executable SPipe definition; no execution result is embedded.

## Scenarios

- binds executable compiler runtime and bundle authorities
- is stable when every producer authority is unchanged
- binds the selected ABI v1 epoch
- binds the selected ABI admission identity
- requires an explicit admitted receipt and rejects absent policy
- rejects receipt policy and runtime mismatches
- rejects duplicate admission fields rather than choosing one
- binds a matching admitted receipt digest into producer identity
- rejects a valid-looking receipt admitted for a different compiler
- rejects a mutated admission identity instead of trusting receipt text
- rejects a mutated evidence digest even when the compiler digest still matches
- rejects a non-canonical compiler digest before receipt admission

## Selected Policy

ABI policy is v1. Deferred or compatibility-zero admission is not authoritative.

## Freshness

The requirement IDs and scenario titles mirror the executable source. No
runtime PASS is claimed.
