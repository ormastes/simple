# Signed Artifact Receipt v2

SAM2 is the canonical Ed25519 signing body for a SimpleOS artifact observation.
It binds the SHA-256 digest, exact positive byte count, bounded launch role,
bounded authority identity, complete target triple, canonical installation path,
ordered aliases, entrypoint, signature algorithm, signer key ID, and signing
public-key digest. SCR2 is the canonical envelope containing the
SAM2 bytes, detached `ed25519:<key-id>:<signature-hex>` signature, and expected
SHA-256 identity of the signing public key.

The common structural codec owns byte order, bounds, exact-end parsing, and
canonical re-encoding. The installer producer derives the Ed25519 public key
from a 32-byte seed, signs only SAM2, self-verifies, and emits SCR2. The loader
verifier selects exactly one configured signer policy, rejects duplicate key
IDs and public keys, checks its public-key identity, verifies the signature over
the retained SAM2 bytes, enforces its authority, role, and target allowlists,
and compares every signed subject field with the guest's independently observed
launch expectation.

Production boot policy is supplied by the independently authenticated SBP2/SBE2
contract described in
`doc/05_design/os/loader/signed_artifact_receipt_boot_policy_v2.md`. It projects
bounded authority, role, and exact multi-architecture target allowlists into the
verifier policy only after a compiled architecture boot root authenticates the
policy file. The SCR2 subject and the policy file cannot nominate their own
authenticating root.

The public guest result is deliberately non-authorizing: it contains only
`ok` and a diagnostic reason, never an executable capability or loader receipt.
The controlled compatibility decoder can classify and decode canonical SCR1
for migration inventory, but the guest verifier calls it with legacy disabled;
an SCR1 therefore cannot satisfy an SCR2-required launch.

Limits are 256 KiB per SCR2, 128 KiB per SAM2, 64 aliases, 4 KiB for each path
or entrypoint, 128 bytes for authority identity, and 64 bytes for role and each
target-triple component. Decode work and retained memory are linear in the
bounded receipt size. The codec rejects trailing data and noncanonical forms.

Static specifications cover tampering with artifact length, role, authority,
target, and digest while retaining the original signature, plus exact-end and
legacy-format rejection. Runtime evidence remains intentionally outstanding
for this unverified implementation lane.
