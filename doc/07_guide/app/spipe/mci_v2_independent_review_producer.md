# MCI-v2 independent reviewer producer

This is the second admission pass. First run the aggregate collector without a
reviewer and preserve its report and candidate graph byte-for-byte. A separately
administered human reviewer signs a canonical decision binding `run_id`,
`source_hash`, `configuration_hash`, and `aggregate_candidate_sha256`.

The reviewer policy pins the reviewer public-key hash, role, scope, and mode.
Reviewer and producer keys must have different IDs and bytes. A live decision
must approve `MCI-NFR-017,MCI-NFR-018` within the 24-hour window.

## Two-pass workflow

1. Run `check-mci-v2-aggregate.shs` with all nine non-review lane receipts. It
   publishes the frozen `aggregate-candidate-v1.env` beside the blocked first-
   pass report; its SHA-256 is the report's candidate identity.
2. Fill a decision with the exact report identities, candidate hash, reviewer
   identity, decision, and validity window.
3. Sign it separately: `openssl dgst -sha256 -sign REVIEWER_PRIVATE.pem -out reviewer.sig decision.env`.
4. Run `check-mci-v2-independent-review.shs` with the report, graph, decision,
   signature, policy, and both public keys. Its usage is the authoritative flag
   list.
5. Re-run the aggregate collector using the activated reviewer generation.
   The collector snapshots `reviewer-generation.current`, requires it to name
   the current candidate digest, validates the generation directory and exact
   four-field `complete.env`, re-hashes the receipt and signature, then applies
   the normal canonical receipt and detached-signature checks.

The producer stages `reviewer.receipt`, `reviewer.sig`, and `complete.env` in
one generation directory, then activates it through
`reviewer-generation.current`. Consumers must resolve only that marker. A
failure before activation publishes nothing and may be retried with unchanged
inputs. Preserve collisions; create a fresh candidate instead of overwriting
reviewed evidence.

The content-addressed generation is the preferred live interface. A legacy
flat `receipts/reviewer.receipt` plus `signatures/reviewer.sig` remains accepted
only when no activation marker exists; it receives the same strict canonical,
identity, freshness, candidate-hash, and signature validation. Once a marker
exists, the collector never falls back to flat files on a malformed, stale, or
incomplete generation.

`--contract-fixture` emits `artifact_mode=CONTRACT_ONLY` and
`release_eligible=false`; it cannot authorize a release.
