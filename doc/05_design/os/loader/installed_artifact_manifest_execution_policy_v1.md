# Installed-artifact manifest execution policy v1

Status: implemented, static-only, unverified.

## Boundary

The policy owner joins the compile-time active SimpleOS target to a sealed,
generation-revalidated installed-artifact catalog row before source I/O. It
admits only ELF64 rows for the mapping-ready x86-64, AArch64, and RV64 process
image owners. The resulting value contains catalog metadata, a fresh pure load
consumer, and the signed resource-limit projection; it contains no file handle
or execution authority.

The filesystem admission wrapper requires the canonical manifest identity and
content digest to match the catalog row before delegating to authenticated ELF
reading and authority issuance. There is no path-only fallback.

## Fail-closed compatibility

- Format version must be exactly the canonical loader version.
- Artifact kind must be exactly `elf`.
- Target must equal the compile-time active target and be mapping-ready.
- Every signed capability bit must be present in the child capability mask.
- ABI features must be exactly one `elf64` and one `w_xor_x`.
- Required services must currently be empty because no service-resolution
  transaction is yet carried into scheduler adoption.
- Resource limits must be nonnegative and currently all zero because no joint
  scheduler/descriptor-limit transaction exists. Nonzero signed limits are
  rejected instead of being dropped after authority issuance.
- Namespace templates, native/SMF libraries, interpreters, arguments, and
  preloads must be empty until their canonical downstream owners are carried
  through scheduler adoption.

## Ordering

Catalog generation lookup, bounds, format, kind, target, capability, ABI,
service, resource, canonical manifest identity, and catalog content identity
all complete before the first VFS payload read. Authenticated byte hashing,
ELF layout validation, binding revalidation, and consume-once authority issue
remain owned by the existing loader admission pipeline.

The installed catalog signature and the per-open admission signature cover
different canonical domains. The sealed row retains the public-key digest that
authenticated it at boot. The wrapper requires the exact `ed25519` catalog
scheme/envelope and signer identity to match the per-open proof signer; the
retained digest must equal the admission trust-root hash, and the delegated
verifier proves the per-open signature against that key. It does not require
two domain-separated signatures to have identical bytes. Generic
authenticated-media APIs retain their prior behavior;
only the installed-artifact entrypoint applies this catalog policy.
