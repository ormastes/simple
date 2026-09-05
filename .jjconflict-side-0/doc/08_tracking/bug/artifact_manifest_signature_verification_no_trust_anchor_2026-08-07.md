# `SimpleArtifactManifest.signature` has a real Ed25519 primitive available but NO trust-anchor/key-distribution infra to call it meaningfully

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
