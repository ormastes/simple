# SimpleOS loader catalog population owner blocker

## Status

Blocked on canonical boot ownership. The target-bound installed-artifact
lookup is implemented and package-private, but it cannot yet be made mandatory
in the authenticated filesystem admission API without disabling all of that
API's current architecture-fixture callers.

## Static evidence

- `installed_artifact_catalog_bootstrap_begin_v1`, `_add_v1`, and `_seal_v1`
  have no production caller under `src/`; their only callers are the catalog
  unit specification.
- The authenticated filesystem admission callers construct manifests directly
  in architecture fixtures. They do not receive a sealed installed-artifact
  catalog from a boot/image owner.
- `executable_loader_admit_authenticated_open_binding_v1` currently maps only
  `x86_64`, `aarch64`, and `riscv64` into the ELF layout owner. The ELF owner
  supports all six architecture enum values, but canonical admission does not.
- The signed Simplebox catalog producer contract currently names x86_64,
  aarch64, riscv64, and riscv32. It has no signed x86-32 or ARM32 target row.

Consequently, an unconditional lookup returns `nil` for all existing boot
paths. An optional lookup, a caller-provided fallback manifest, or a second
launcher-local catalog would preserve the bypass and is not an acceptable
hardening change.

## Required ownership transfer

The canonical image/boot owner must, before starting any filesystem launcher:

1. decode and authenticate each bounded signed catalog record against the boot
   trust root;
2. begin one loader-package bootstrap session, add the target image's complete
   catalog (currently at most 16 records), and seal it exactly once;
3. transfer the platform owner's exact `ManifestTarget` to loader admission;
4. cover x86_64, x86, aarch64, arm, riscv64, and riscv32 across the target-image
   build/boot matrix, with each boot catalog containing only its exact target's
   rows; and
5. fail boot closed if population, sealing, or target coverage is incomplete.

The catalog is keyed by path rather than `(path, target)`, so rows for several
targets with the same canonical path cannot coexist: duplicate paths are
rejected. Loading all six target variants into one catalog is therefore not a
valid substitute for target-specific image population. If an image needs more
than 16 installed executable records, owner capacity must be redesigned rather
than silently truncating the image catalog.

After that transfer exists, canonical admission can safely perform exactly one
`installed_artifact_catalog_lookup_target_v1(binding.canonical_source_path,
platform_target)` before reading executable bytes. Target mismatch will then be
rejected inside the catalog owner before nested copy and integrity hashing. The
returned catalog manifest should replace the duplicate caller manifest, scalar
digest/signer/format bindings should be checked before I/O, and the existing
single filesystem read, SHA-256 pass, ELF parse, and authority issue should
remain the only hot-path work.

## Acceptance evidence needed

- Static ownership coverage showing one boot producer and no alternate catalog.
- Static admission coverage for all six target-image tuples and alias/canonical
  paths, including alias collision and the 16-record capacity boundary.
- Rejection cases for unsealed catalog, absent row, target mismatch, digest
  mismatch, signer mismatch, and stale execute binding.
- Success coverage proving one expected-O(1) lookup (bounded worst case: 256
  probes plus bounded deep copy/integrity hashing), one image read/hash, one ELF
  layout pass, and one consume-once authority issuance.

No runtime verification was run while recording this blocker, per user request.
