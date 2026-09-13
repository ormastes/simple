# Verified SimpleOS image composition owner v1

Requirement: `REQ-SIMPLEOS-VERIFIED-IMAGE-OWNER-V1`

## Materialize exact admitted bytes

Place the real kernel, init service, loader, and variant selector beneath one
trusted absolute directory. The owner retains that directory as a no-follow
descriptor authority, reads each named relative input exactly once, derives
its SHA-256 identity, persists it into the DBFS-backed NVFS root, and reopens
the persisted namespace to compare every file with its source bytes.
Before persistence, the kernel must pass the shared loadable x86_64 ELF gate;
init, loader, selector, and optional compiler must pass the canonical x86_64
SimpleOS SMF envelope and embedded-ELF gates. Opaque text and wrong-target
payloads never become target metadata.

The raw image is published as a new relative leaf through the atomic hosted
provider. Existing output is never replaced. The owner reads the published
leaf back through the same retained root and compares byte length and SHA-256
before it creates the materialization receipt.

## Compose the shared manifest

After materialization, the owner projects the byte-derived artifact evidence
into `SimpleOsImageManifestV1` and submits the exact x86_64 candidate to the
canonical composer. The returned manifest and receipt therefore agree on the
carrier/root identity, required baseline roles, profile, build identity, and
SOSIX version. A compiler payload is accepted only for the `dev` profile.

## Fail-closed boundaries

Traversal, absolute relative-path operands, duplicated source/output paths,
empty artifacts, oversized sources or images, pre-existing outputs, reused
manifest buffers, persisted readback mismatches, and manifest mismatches are
rejected. The owner accepts no descriptor fallback, placeholder payload,
caller proof boolean, release signature, or publication grant.
