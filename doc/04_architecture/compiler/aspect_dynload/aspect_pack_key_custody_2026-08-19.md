# Aspect-pack signature key custody (E-APACK003)

Status: OPEN. Signature checking (`apk_verify_signature_v1` in
`src/lib/common/aspect_pack.spl`) is implemented and fail-closed, but the
operational trust root does not exist. Until the questions below are answered
and the answer is *implemented* (not just written down), every caller MUST
use `apk_signature_policy_disabled()` and signature checking MUST stay off.

## Why this doc exists

A prior attempt at this feature shipped a verifier that checked packs against
a public key stored in the same repository as the packs. That is worse than
no check: it is green on any attacker-controlled input, because the attacker
controls both the pack and the "trust root" sitting next to it. Content-hash
verification (also in `aspect_pack.spl`, disjoint error codes
`APK_CONTENT_HASH_*`) is honest today — it is a real corruption detector.
Signature verification is not honest until every question below has an
operational answer, not a design-doc answer.

## Open questions

### 1. Who signs, and at what build step?

Not yet decided. Candidates: (a) the release-build pipeline signs each
aspect-pack SMF as the last step before publishing, using a key held by CI,
not by any individual developer machine; (b) a separate, out-of-band signing
service that the build pipeline calls, so the signing key never touches the
same machine that compiles arbitrary source. (b) is the harder-to-compromise
option in a compiler whose build touches an enormous amount of low-trust code
(the compiler compiles itself); it has not been built.

### 2. Where does the private key live?

Not yet decided. It must NOT live in this repository (checked-in secrets are
exactly the anti-pattern this doc exists to prevent), and it must not live
on any developer's workstation. It needs a real secret store (HSM, KMS, or
equivalent) with access scoped to the release pipeline's identity only, plus
an audit log of every signing operation. None of that infrastructure exists
in this codebase yet.

### 3. How does the public trust root reach the verifier WITHOUT shipping beside the packs?

This is the crux of the original refusal. If the trust root ships in the
same artifact stream as the packs (same repo, same release tarball, same
directory), an attacker who can replace one can replace both, and the check
verifies nothing. The trust root must reach the verifier through a channel
with an independent compromise boundary — for example: pinned into the
`simple` toolchain binary itself at a release built and reviewed separately
from aspect-pack content, or fetched from a dedicated key-distribution
endpoint the pack repository has no write access to, with pinning/TOFU
handled explicitly. Neither is implemented. Until one is, any
`ApkSignaturePolicyV1` with `has_trust_root: true` used outside a test is a
bug, not a feature.

### 4. Rotation

Not yet decided. A rotation plan needs: an overlap window where both the old
and new key verify successfully (so in-flight packs signed under the old key
are not spuriously rejected), a revocation mechanism for a compromised key
(distinct from routine rotation), and a record of which key signed which
pack for forensics. None of this exists; `ApkSignaturePolicyV1` today carries
exactly one trust-root key with no rotation or revocation support.

### 5. What happens on verification failure?

Answered by the implementation, restated here for the record:
`apk_verify_signature_v1` never returns `ok: true` except on a signature that
positively verifies against a configured trust root. Every other case —
no trust root (`APK_SIGNATURE_NO_TRUST_ROOT` when a signature is present,
`APK_SIGNATURE_CHECK_DISABLED` when checking is simply off), a required
signature that is missing (`APK_SIGNATURE_REQUIRED_MISSING`), a malformed
signature (`APK_SIGNATURE_MALFORMED`), or a signature that fails to verify
(`APK_SIGNATURE_INVALID`) — is a distinct, disjoint error code from every
`APK_CONTENT_HASH_*` code, so a caller can never mistake an integrity pass
for an authenticity pass. What the LOADER does with a refusal (hard-fail
the load vs. degrade to an unsigned/lower-trust mode) is a policy decision
for whichever caller wires this in, and is out of scope for this doc.

## Until this is answered

Every caller in this tree uses `apk_signature_policy_disabled()`. Signature
checking exists as tested, fail-closed plumbing — not as an enabled security
control. Enabling it for real traffic requires closing questions 1-4 above
with running infrastructure, not just a written answer.
