# SPipe Knowledge Compiler Refactor Recovery — Authored Design Scaffold

> **Not generated and not PASS evidence.** Transaction oracles are unresolved,
> so the executable scaffold fails explicitly.

**Source:** `test/03_system/app/spipe/feature/spipe_knowledge_compiler_refactor_spec.spl`  
**Generation command:** `bin/simple spipe-docgen test/03_system/app/spipe/feature/spipe_knowledge_compiler_refactor_spec.spl --output doc/06_spec --no-index`

## REQ/NFR map

- Identity/registry: REQ-SPKC-002, 005; NFR-SPKC-009..010, 023.
- Plan/apply/recovery: REQ-SPKC-019..020, 026, 029; NFR-SPKC-004..006, 008.
- Platform/evidence: NFR-SPKC-019..022.

## Operator flow

Apply a transactional refactor only from a snapshot-bound, principal-bound,
single-use approval. Inspect durable before-images, lock order, hash chain,
aliases, references, governed metadata, and rollback map. On interruption run
doctor/recovery; never hand-complete a partial move.

## Fault and race matrix

Inject failure at lock, token consumption, before-image fsync, Prepared, every
replace, file/directory fsync, Applying, validation, manifest switch, Committed,
receipt fsync, and unlock. Include partial write, disk full, permission loss,
revocation, concurrent edit, kill/reboot, replay/expiry, symlink swap, unknown
journal major, and cross-device move. Accept only exact old state, exact new
state, or preserved `recovery_required`; expected typed rejects also include
`precondition_failed`, `unauthorized`, `transaction_conflict`, and
`unsupported_version`.

## Evidence limitation

Retain artifact/log receipts with content and metadata hashes. The current
helpers raise `DESIGN-SCAFFOLD`; no transaction PASS is claimed.
