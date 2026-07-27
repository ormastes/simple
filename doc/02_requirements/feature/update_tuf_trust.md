# Feature Requirement — TUF-style Signed Update Trust Model

**Domain:** os / updates & recovery
**Master plan:** §20 (updates/recovery), §22 Phase 5 exit gate (compromised-update simulations)
**Status:** Model (Phase 5 groundwork)
**Owner model:** `src/os/services/update/tuf_metadata.spl`
**Spec:** `test/01_unit/os/services/update/tuf_metadata_spec.spl`

## Purpose

SimpleOS updates must remain secure even when the update repository is
compromised or a single signing key is stolen. This feature models the trust
structure of The Update Framework (TUF): four cooperating roles with delegated
signing keys and thresholds, plus freshness, rollback, and consistency
defenses. It is the trust-model layer beneath signed packages, transactional
A/B install, and rollback required by §20.

**Modeled vs. real.** This increment is a pure model: signatures are
represented as an already-verified key-id list (`signatures_present`); there is
NO real cryptography, network pull, or package install. The value delivered is
the *trust-structure verifier* — the part that decides whether a set of
presented metadata should be accepted — which is exactly what defends against
repository/key compromise. Real signature verification and install are the next
increment (see Forward requirements).

## The four TUF roles and what each protects

| Role | Protects |
|------|----------|
| **root** | Trust anchor. Holds/delegates the signing keys for every other role; establishes the set of trusted keys. Compromise of any non-root key does not extend authority beyond what root delegated. |
| **targets** | Vouches for the actual update artifacts — name, length, digest, version. Prevents substitution of arbitrary or tampered artifacts. |
| **snapshot** | Pins a mutually consistent set of role versions. Prevents mix-and-match attacks where an attacker pairs fresh metadata for one role with rolled-back metadata for another. |
| **timestamp** | Short-lived, frequently re-signed pointer to the current snapshot. Its expiry is how clients detect a freeze attack (a repository that stops serving updates to hold clients on vulnerable versions). |

## Defenses (each is a verifier function + an oracle in the spec)

1. **Threshold signing** (`verify_threshold`): a role is accepted only when at
   least `threshold` *distinct* keys that are authorized to sign that role have
   signed. A single stolen key below threshold cannot forge a role. Fail-closed
   reason: `TUF_BAD_THRESHOLD`.
2. **Freshness / freeze defense** (`check_freshness`): metadata past its
   `expires_at` (relative to a caller-supplied `now`, never a clock call) is
   rejected. Blocks freeze attacks that pin clients on stale, vulnerable
   metadata. Reason: `TUF_EXPIRED`.
3. **Rollback defense** (`rollback_guard`) — the KEY TUF property: an incoming
   version below the locally trusted current version is rejected, so a validly
   signed but *older* metadata cannot be replayed to reintroduce known-
   vulnerable artifacts. Reason: `TUF_ROLLBACK`.
4. **Snapshot consistency** (`verify_snapshot_consistency`): the targets version
   snapshot vouches for must equal the presented targets version, blocking
   single-role rollback / mix-and-match. Reason: `TUF_SNAPSHOT_MISMATCH`.
5. **Root-anchored key trust** (`keys_trusted_by_root`): every presented
   signature must trace to a key in root's trusted set; a signature from any
   other key is rejected. Reason: `TUF_UNTRUSTED_KEY`.

`verify_update` runs these in order and fails closed with the first failing
reason, giving each compromise scenario a distinct, testable outcome.

## Acceptance oracles (spec)

- A well-formed update — threshold-signed, fresh, forward-versioned, snapshot-
  consistent, root-trusted keys — is ACCEPTED (`TUF_ACCEPTED`).
- Each of the five attacks is REJECTED with its distinct reason code:
  below-threshold, expired (freeze), rollback, snapshot mismatch, untrusted key.
- Fail-once proof: disabling `rollback_guard` makes the rollback-attack oracle
  fail (accepted instead of `TUF_ROLLBACK`), demonstrating the test truly gates
  the property.

## Forward requirements (next increments, not in this model)

- **Real signature verification** via the crypto/signature stack: replace the
  modeled `signatures_present` verified-key-id list with actual public-key
  signature checks over canonicalized metadata.
- **Transactional A/B install + rollback**: apply verified updates to an
  inactive slot, health-check, then atomically switch; revert on failure.
- **SLSA provenance attestations**: build artifacts must carry verifiable
  provenance (builder identity, source revision, build parameters) that is
  checked alongside TUF targets metadata before an artifact is installed. This
  binds "what was built and how" to "what is trusted to install."
- **Key rotation & offline root**: model/implement root key rotation and
  offline root signing ceremonies per §20.
