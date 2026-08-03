# Spec-to-SPipe Phase 0 Verification Test Plan

Status: Initial verifier slice; A0 shared-model integration remains open.

## Scope

This plan covers the A2 fail-closed gates that protect the frozen importer
contracts before format adapters are allowed to merge. It does not claim that
the shared A0 manifest and source models are implemented; verifier-owned input
records are temporary adapters to those forthcoming models.

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

When A0 publishes shared records, adapt `SourceDispositionSpan`,
`RecoveryRecord`, and `VerificationManifestIdentity` at the verifier boundary.
Keep `verify_exact_coverage`, `verify_no_silent_recovery`, and
`verify_manifest_identity` stable. The shared manifest must provide raw byte
length, ordered disposition spans, recovery diagnostics, approved adapter rule
IDs, expected schema/version, and independently observed source SHA-256.

## Acceptance command

```sh
bin/simple test test/01_unit/app/spec_to_spipe/verify_spec.spl --mode=interpreter
```

The gate passes only when all deliberate-red fixtures are rejected for their
intended reason and the two well-formed fixtures are accepted.
