# Spec-to-SPipe Phase 0 Verification Test Plan

Status: Phase 0 verifier gates consume the shared A0 manifest contracts.

## Scope

This plan covers the A2 fail-closed gates that protect the frozen importer
contracts before format adapters are allowed to merge. Coverage, recovery, and
identity gates consume A0's shared ledger, `SpecErrorNode`, and manifest types.

## Requirement traceability

| Requirement | Production gate | Evidence |
|---|---|---|
| REQ-S2S-COV-001 | `verify_exact_coverage` | Accepts exact adjacent coverage; rejects gaps, overlap, invalid spans, unknown dispositions, and exclusions without reasons. |
| REQ-S2S-REC-001 | `verify_no_silent_recovery` | Accepts only source-preserving, diagnostic-bearing, manifest-approved compatibility recovery; strict mode rejects all recovery. |
| REQ-S2S-ID-001 | `verify_manifest_identity` | Rejects unknown schemas, missing/floating identity, stale versions, malformed digests, and stale source hashes. |

## Deliberate-red fixtures

The unit specification seeds dropped bytes, overlapping bytes, an unreasoned
`unsupported` span, silent recovery, an unapproved adapter rule, strict-mode
recovery, an unknown schema, a floating version, a malformed digest, and stale
source content. Every fixture invokes a production verifier and asserts its
stable rule ID; there are no source-grep or tautological passes.

## Determinism contract

Inputs are evaluated in canonical source order and diagnostics are appended in
stable rule order. The coverage gate intentionally rejects out-of-order spans
instead of sorting them implicitly. The gates perform no file, environment,
clock, process, network, or random access.

## A0 integration boundary

Integration is complete for the Phase 0 gates. The verifier defines only
`SpecVerificationResult`; all source, ledger, recovery, and identity input
records come from A0. Future adapters must not restore verifier-private copies.

## Acceptance command

```sh
bin/simple test test/01_unit/app/spec_to_spipe/verify_spec.spl --mode=interpreter
```

The gate passes only when all deliberate-red fixtures are rejected for their
intended reason and the two well-formed fixtures are accepted.
