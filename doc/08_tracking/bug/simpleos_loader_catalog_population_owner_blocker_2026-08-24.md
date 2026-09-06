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
- `executable_loader_admit_authenticated_open_binding_v1` now maps all six
  canonical userland architecture spellings into the existing ELF layout
  owner. This closes the parser-dispatch prerequisite, but does not populate or
  seal the installed-artifact catalog and therefore cannot make catalog lookup
  mandatory yet.
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

The former path-only key and 16-record global capacity blocker is resolved by
the target-scoped catalog redesign: keys now contain `(path, os, arch, abi)`,
each of the six SimpleOS targets owns a 16-record partition, and the bounded
owner retains at most 96 records. Identical canonical paths and aliases may
coexist across targets without collision. Boot population and ownership
transfer remain deliberately unwired, so this blocker is not otherwise closed.

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
  paths, including same-path cross-target coexistence, path-only ambiguity
  rejection, and each 16-record target capacity boundary.
- Rejection cases for unsealed catalog, absent row, target mismatch, digest
  mismatch, signer mismatch, and stale execute binding.
- Success coverage proving one expected-O(1) lookup (bounded worst case: 2048
  probes plus bounded deep copy/integrity hashing), one image read/hash, one ELF
  layout pass, and one consume-once authority issuance.

No runtime verification was run while recording or updating this blocker, per
user request.
