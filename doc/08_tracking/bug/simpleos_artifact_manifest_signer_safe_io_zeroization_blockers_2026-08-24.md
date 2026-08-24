# SimpleOS artifact manifest signer safe-I/O and zeroization blockers

Status: OPEN — unsafe signer draft reverted after independent static review.

The canonical SAM1 signing codec is available, but a robust build-time
`simpleos_artifact_manifest_signer` cannot yet be implemented on the current
host facade without weakening the requested security properties:

1. `src/os/installer/image_bounded_file_reader.spl` records that hosted file
   reads have no O_NOFOLLOW/openat2 handle whose `fstat` identity and bounded
   reads remain tied to the validated object. A path predicate and size check
   followed by a path reopen is TOCTOU-vulnerable for the artifact, descriptor,
   raw seed, and trust configuration.
2. The app-facing I/O owner has no implemented create-exclusive staged byte
   writer plus rename-no-replace operation. A predictable staged path and
   check-before-rename can follow or overwrite a raced path and can replace a
   destination created after the check.
3. `pure_ed25519_sign` retains derived secret arrays (`h`, clamped scalar,
   prefix/nonce material, reduced scalars, and multiplication inputs). Wiping
   only the caller's raw seed does not satisfy whole-operation secret-buffer
   zeroization.

Required prerequisites are therefore:

- a pure-Simple typed hosted file owner that opens no-follow, snapshots identity
  and size with `fstat`, performs bounded reads on that same handle, and closes
  exactly once;
- a create-exclusive, no-follow staging handle and atomic rename-no-replace
  publication primitive; and
- a zeroizing pure-Simple Ed25519 public-key derivation/signing entrypoint that
  reports wipe failure and clears all derived secret workspaces.

After those land, the signer can strictly parse exactly one key id/public
key/public-key-hash trust record, require the manifest's content-hash vector to
equal the singleton artifact hash, sign canonical SAM1 bytes, self-verify, and
emit a versioned full record whose decoder rejects trailing data.

No tests, builds, lints, optimizer, SPipe, benchmarks, or runtime verification
were run. This record is based on read-only source inspection.
