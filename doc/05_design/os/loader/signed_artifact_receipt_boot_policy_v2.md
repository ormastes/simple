# Signed Artifact Receipt Boot Policy v2

`SBP2` is the canonical signing body for the policy that delegates verification
of `SCR2` artifact receipts. `SBE2` contains that body, the boot signer key ID,
one raw Ed25519 signature, and the expected SHA-256 identity of the boot public
key. The canonical boot-media path is `/boot/catalog/scr2-policy.sbe2` and the
complete envelope is limited to 64 KiB.

The policy authenticating root is not in the policy. On x86_64, AArch64, and
RV64, the loader adapters obtain the key ID and public key from the existing
generated architecture trust configuration compiled into the boot image. The
SBE2 key ID and root hash must match that independently supplied root before
signature verification. Presence, successful decoding, a subject assertion,
or a public key carried by the file grants no authority. Private seeds are not
part of this contract or loader path.

The authenticated subject binds one delegated SCR2 signer key ID, its exact
32-byte Ed25519 public key and SHA-256 identity, bounded unique authority and
role allowlists, and exactly these target triples in canonical order:

1. `simpleos/x86_64/simpleos`
2. `simpleos/aarch64/simpleos`
3. `simpleos/riscv64/simpleos`

Wildcards, duplicate identities or roles, reordered, missing, additional, or
non-SimpleOS targets, unknown versions, noncanonical encodings, trailing bytes,
and hash/key disagreement fail closed. After authentication, the loader projects
the subject into `SignedArtifactReceiptTrustPolicyV2`. Each architecture adapter
then proves its exact local target occurs once and narrows the result to that
singleton. This value-based scan does not trust media ordering: x86_64,
AArch64, and RV64 adapters cannot return authority for either of the other
architectures. Missing, duplicate, or cross-architecture local grants fail
closed. Broad authentication state stays private to the owner module; adapters
return the distinct `SignedArtifactReceiptLocalBootPolicyAdmissionV2` shape,
which carries the exact local target beside its singleton trust policy. The
projection remains diagnostic verification policy; it is not an executable-
authority token.

The loader reads the policy through one bounded stable VFS snapshot and retains
only its closed observation seal. An absent, oversized, malformed, tampered, or
wrong-root policy leaves SCR2 launch trust unavailable. Installer-side policy
signing or emission is intentionally separate and is not implemented here.

## Static acceptance cases

- An independently rooted valid SBE2 projects one bounded SCR2 policy.
- Byte tampering and substitution of the boot root are rejected.
- Duplicate authorities/roles and wildcard overbreadth are rejected.
- The target set must be exactly x86_64, AArch64, and RV64 SimpleOS.
- Each architecture adapter exposes only its singleton local target and rejects
  cross-architecture, omitted, and duplicate local grants.
- Trailing and noncanonical bytes are rejected.

These cases are specified in
`test/01_unit/os/kernel/loader/signed_artifact_receipt_boot_policy_v2_spec.spl`.
They were authored under a no-execution instruction and therefore require a
later admitted self-hosted verification run.
