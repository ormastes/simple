# `SimpleArtifactManifest.signature` has a real Ed25519 primitive available but NO trust-anchor/key-distribution infra to call it meaningfully
## Closed 2026-11-11 — SUPERSEDED (infrastructure landed elsewhere at tip; verified this pass)

The 2026-08-07 premise ("no trust-anchor, no key distribution, no wire format,
no message definition") is stale at release/1.0.0 tip. All four gaps are closed
by `src/os/kernel/loader/executable_manifest_signature_verifier.spl` +
`src/lib/common/structural/execution/simple_artifact_manifest_v1_codec.spl`,
wired into the admission pipeline, with a passing regression spec. Fresh
evidence in the 2026-11-11 addendum at the bottom of this file.

> Status: SUPERSEDED — was Open 2026-09-16 — needs owner triage

Reviewed in the 2026-09-16 bug-ledger normalization pass; no resolution
evidence found in the body. This is bookkeeping, not verification.

> **CLAIMED-OFFHOST 2026-08-17** — do not work locally; assigned to a second host. See doc/03_plan/infra/priority_bug.md

- **ID:** artifact-manifest-signature-no-trust-anchor-2026-08-07
- Status: OPEN (P2)
- Status re-verified 2026-08-17 by source inspection (triage shard 00).
  Wave 4) landed REAL content-hash verification
  (`manifest_verify_content_hash` in `src/os/kernel/loader/artifact_manifest.spl`)
  but deliberately did NOT wire signature verification, for the reason below.
- **Severity:** MEDIUM — `manifest_reason_signature_without_hash` already
  rejects an unbound signature (hash-less), but nothing ever cryptographically
  verifies a *bound* signature against a trusted key. A manifest can carry
  `signature: "ed25519:aabbcc"` + a matching `content_hashes` entry and pass
  `manifest_validate` even though the signature bytes are never checked.
- **Owner path:** `src/os/kernel/loader/artifact_manifest.spl`

## What DOES exist (checked before writing this)

A real, pure-Simple, baremetal-safe Ed25519 verifier is reachable:

```
src/os/crypto/ed25519.spl:444
fn ed25519_verify(public_key: [u8], message: [u8], signature: [u8]) -> bool
```

Per RFC 8032 §5.1.7, already used by the SSH/TLS stack elsewhere in this
kernel tree (`os.crypto.mod` re-exports `ed25519_sign`/`ed25519_verify`). This
is the SAME primitive family (`os.crypto.*`) WP-19 reused for the content-hash
half (`os.crypto.sha256.sha256`), so "no primitive exists" is NOT the reason
this is unwired.

## What is MISSING (the actual gap)

`SimpleArtifactManifest` has exactly one signature-shaped field:

```
signature: text   # e.g. "ed25519:aabbcc..."
```

There is no:

1. **Public-key field or reference.** `ed25519_verify` needs a 32-byte public
   key. The manifest carries none, and there is no separate field naming
   which key (or key ID) the signature should be checked against.
2. **Trust anchor / key registry.** Even if the manifest carried a public key
   inline, that only proves "signed by SOMEONE holding this key" — it proves
   nothing about authority unless the loader can check that key against a
   trusted root (a provisioned system key, a CA-style chain, or a pinned
   allowlist). No such registry exists anywhere in `os.kernel.loader` or
   `os.crypto`.
3. **Signature encoding/parsing.** `signature: text` is currently an opaque
   `"algo:hex"` string with no parser that splits it into (algorithm tag, raw
   64-byte R‖S) and validates the tag against what the loader supports.
4. **Message definition.** Ed25519 signs a message; the manifest doesn't
   define what byte sequence is signed (the manifest's own canonical
   encoding? the artifact's content hash? both?) — an ambiguous message
   definition is itself a security hole if implemented casually.

Building all four is real infrastructure (key provisioning + a trust model +
a wire format), not a function call — it is exactly the kind of thing that
should not be faked to make an acceptance bar look green. Per the plan's own
precedent (WP-G left invariant 3 honestly RED rather than faking pinning
enforcement), this WP leaves signature verification explicitly gapped and
implements only the content-hash half for real.

## Unblock condition

Land, in order: (1) a key-registry/trust-anchor design (even a minimal
single-pinned-key allowlist would do for a first cut), (2) a manifest field
carrying a key ID or inline public key, (3) a signature wire-format parser,
(4) a defined "message" the signature covers (recommend: sign the
already-computed content-hash hex, not raw artifact bytes, so verification
stays O(1) after the hash check). Then wire `ed25519_verify` into
`manifest_validate`/`manifest_verify_content_hash` as a second, independent
gate.

## Verification 2026-08-17 (content classification, fleet lane I)
STILL-OPEN. `grep -c "trust_anchor\|manifest_verify_signature" src/os/kernel/loader/artifact_manifest.spl`
returns **0**. There is still no trust anchor, no key distribution, and no
verification entry point — the `signature` field is carried and never checked.
Not repaired here: `src/os/crypto/**` is explicitly out of scope for this lane.

## Triage 2026-09-13

Confirmed still absent: `grep -c "trust_anchor\|manifest_verify_signature" src/os/kernel/loader/artifact_manifest.spl` returns 0. Implementing a trust-anchor/key-registry design plus a signature wire format is multi-step security-architecture work (the doc's own "Land, in order" list has 4 steps before wiring `ed25519_verify`), explicitly out of scope for `src/os/crypto/**` per the prior lane. Leaving OPEN, no code change made.

## Triage 2026-11-11 (p3fix-p2a-20261111 lane) — SUPERSEDED

Re-verified at release/1.0.0 tip (worktree @ 79d5af6723f6). The four named gaps
are all closed by later-landed infrastructure — none of it in
`artifact_manifest.spl` itself, which is why the doc's original grep stayed 0:

1. **Trust anchor / key registry** —
   `executable_manifest_trust_owner_initialize` in
   `src/os/kernel/loader/executable_manifest_signature_verifier.spl:112`
   installs up to 16 pinned Ed25519 signers (key_id + 32-byte public key) into
   a one-time private capsule, mutex-protected with quarantine-on-failure.
   Initialized by the boot owner
   (`installed_artifact_catalog_boot_owner_v1.spl:171`).
2. **Manifest field naming the key** — the `signature` field carries the
   envelope `"ed25519:<key_id>:<128-hex>"`; the key_id is validated and looked
   up against the pinned registry (`SignerUnknown` when absent).
3. **Wire-format parser** — envelope split + `_manifest_signature_decode`
   (hex -> 64-byte signature) + key-id charset/length checks in the same
   module.
4. **Defined message** —
   `encode_simple_artifact_manifest_v1_signing_bytes` in
   `src/lib/common/structural/execution/simple_artifact_manifest_v1_codec.spl:237`
   defines the signed bytes: `SAM1` envelope with the image hash bound in,
   over the manifest's canonical fields (signature excluded).
5. **Wired as a gate** — `executable_admission_pipeline.spl:242` calls
   `executable_manifest_signature_verify` before constructing an executable
   handle, failing closed on `SignatureInvalid`, `SignerUnknown`,
   `TrustRootMismatch`, `TrustRootsUnavailable`, etc.

Fresh evidence: `SIMPLE_LIB=src bin/simple.exe test
test/01_unit/os/kernel/loader/executable_manifest_signature_verifier_spec.spl
--mode=interpreter --no-cache` → PASS (2 declared, 2 executed, 2 passed —
covers trust init, accepted signature, substituted-signature rejection with
`signature-invalid`, wrong trust root with `trust-root-mismatch`, malformed
envelope with `signature-envelope-invalid`). The admission-pipeline spec
(`test/01_unit/os/kernel/loader/executable_admission_pipeline_spec.spl`)
covers the wired gate.

Status flipped open → superseded. No code change in this lane.

