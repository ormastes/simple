<!-- codex-design -->
# Spec-to-SPipe Shared IR Contract v1

Status: Phase 0 contract freeze
Date: 2026-08-03

## Scope

This contract freezes the smallest shared boundary required before census,
verification, parser, adapter, emitter, and semantic-diff lanes proceed. It
does not implement an adapter or claim that a source has been converted.

The public root records are `SpecImportManifest`, `SpecSourceIdentity`,
`SpecDisposition`, `SpecLedgerEntry`, `SpecImportDiagnostic`, and
`SpecErrorNode`, and `SpecVerificationReport`. Version 1 is fail-closed: an
unknown schema name or version is rejected rather than coerced.

## Structural parser reuse

`SpecSourceIdentity.snapshot` is the existing immutable
`std.common.structural.parse.contracts.SourceSnapshot`. Every ledger and
diagnostic range is the existing byte-based `SourceSpan`. No adapter may define
a competing snapshot, span, anchor, or edit contract. Snapshot bytes are hashed
directly with SHA-256; validation rejects stale declared hashes.

## Source identity

Stable source identity hashes length-prefixed provenance in this order:
standard family, published version, edition/date, URI, repository revision or
release tag, source SHA-256, adapter identity/version, and preprocess rule-set
version. `latest` is invalid and the repository revision is mandatory.

Semantic nodes choose identity in the architecture order: explicit upstream
ID, registry ID, fully qualified structural path, adapter semantic key, then a
content plus neighborhood fingerprint. The selected representation includes a
kind prefix so identities from different authorities cannot collide silently.

## Extension namespace

Adapter-specific information is represented only by `SpecExtensionField`.
Namespaces are non-empty dotted names; fields are unique and sorted by
namespace then key. The core does not interpret extension values, so unknown
namespaces survive canonical serialization. An unknown core schema version is
different and is rejected.

## Ledger and recovery invariants

Top-level ledger entries are stable-ordered, in snapshot bounds, and
non-overlapping. Nested syntax relationships belong to the later syntax IR;
they do not justify overlapping top-level byte accounting. Every entry records
a semantic identity, node kind, disposition, adapter rule, reason, and optional
conformance binding.

Diagnostics carry their adapter rule IDs and optional source spans.
`SpecErrorNode` retains its raw source, exact span, diagnostic/rule identities,
recovery state, extensions, and nested error children. Children must remain
inside their parent span. Strict mode rejects every recovery; compatibility
mode accepts only rule IDs explicitly approved by the pinned manifest.
Malformed bytes remain ledger entries with the `Malformed` disposition.

## Deterministic representation

`canonical_spec_import_manifest` emits unambiguous length-prefixed text after
validation. Producer arrays must already be stable-ordered; validation rejects
ambiguous extension or ledger ordering. Canonical output includes unknown
extension triples unchanged and deliberately excludes raw snapshot bytes,
which are addressed by the validated source SHA-256.

## Phase 0 verification report

`verify_spec_import_manifest` reports schema and source-hash validity, exact
byte accounting, malformed bytes, recovery counts, diagnostics, and one final
pass/reason. This report is a shared data contract, not the final A2 release
policy. A2 remains authoritative for round-trip, non-vacuity, deliberate-red,
license, and generated-artifact gates.

The focused A2 entry points consume A0 records directly:
`verify_exact_coverage` accepts ordered `SpecLedgerEntry` values,
`verify_no_silent_recovery` accepts nested `SpecErrorNode` values, and
`verify_manifest_identity` accepts the canonical `SpecImportManifest`.

## Evolution

Fields and meaning in schema version 1 are frozen. Additive adapter data uses
extensions. A core field or semantic change requires a new schema version,
golden fixtures, an explicit migration, and coordinated A0/A1/A2 review.
