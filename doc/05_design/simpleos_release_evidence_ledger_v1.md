# SimpleOS Release Evidence Ledger V1 — Detail Design

**Status:** implemented contract; runtime qualification pending

The ledger is the atomic admission boundary between a complete release-evidence
manifest and later release preparation. It does not sign, publish, or promote.

## Ownership and transition

`SimpleOsReleaseEvidenceLedgerV1` and its entries are copyable inspection
values. They never convey authority. The sole runtime authority is private
module state in `os.services.evidence.release_evidence_ledger_owner_v1`, guarded
by one raw mutex. Owner entry uses the runtime's nonblocking acquisition, so a
contended or permanently poisoned mutex returns `OwnerBusy`/absence instead of
creating an unbounded waiter. Boot must call its one-shot start operation with a validated
durable ledger or explicit genesis; commit is unavailable before that recovery
decision and a second start is rejected. Its commit operation performs, in one critical section:

1. read the canonical head;
2. sample the live authoritative Unix clock;
3. require the claim's exact next sequence and current predecessor digest;
4. reject replayed nonce/evidence identities and invalid time windows;
5. finalize `consumed_at_unix_ms` and `consumed_once` on a local manifest copy;
6. validate and hash that final manifest;
7. derive one claim identity and successor transition digest;
8. assign the next ledger once; and
9. return the finalized manifest and its identities.

All inputs, results, recovery values, and snapshots cross the owner through deep
ledger copies so mutable entry arrays cannot alias canonical state. All
validation failures preserve the prior ledger. Mutex failures quarantine or
fail closed. The embedding evidence service must durably persist the returned
successful snapshot before treating it as restart-stable; V1 does not claim a
storage transaction, signing, or publication.

## Identity and bounds

The genesis digest is SHA-256 of the fixed domain string
`simpleos-release-evidence-ledger-v1:genesis`, never an artifact hash. Each row
stores enough claim inputs for ledger validation to reconstruct the claim hash.
The transition digest binds sequence, predecessor, claim identity, final
manifest digest, and authoritative commit time. History is fixed at 128 rows;
full ledgers reject instead of pruning replay evidence.

## Evidence status

Behavioral specs cover success, stale/competing successors, correction after a
failed manifest, replay, expiry, unavailable and rolling-back clocks,
pre-finalized input, history tampering, exact-sequence mismatch, and capacity.
Pure-Simple runtime execution remains `MissingEvidence` until an admitted
x86_64 self-hosted test runner is available.
