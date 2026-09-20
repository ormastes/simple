# facet_manifest_authority_adapter_spec imports a module that exists nowhere (2026-09-15)
## Open 2026-09-16 — needs owner triage

Reviewed in the 2026-09-16 bug-ledger normalization pass; no resolution
evidence found in the body. This is bookkeeping, not verification.

`test/01_unit/compiler/driver/facet_manifest_authority_adapter_spec.spl`
imports:

- `use compiler.driver.driver_facet_manifest_authority.{facet_manifest_authority_from_source}`
- `use std.common.aspect_pack.{ApkFacetManifestDescriptorV1, ...}`

Neither exists anywhere in the tree today:

- No file under `src/compiler/**` mentions `facet_manifest_authority` or
  `driver_facet_manifest_authority`.
- `src/lib/common/aspect_pack.spl` contains none of the `ApkFacet*` symbols.
- At the spec's own landing commits (e09f6b9ac66, and 01208a07c8d) both were
  already absent — the spec has never been runnable in this repository.

Failure (current binary, after parse fixes): `cannot resolve import
compiler.driver.driver_facet_manifest_authority ... module path segment
'compiler' not found` — hard error, no lane fallback.

## Spec-side fixes already applied (kept)

- `fn facet_test_module(): <dotted.path.Type>:` → invalid return-type syntax;
  fixed to `-> HirModule` with an explicit `use compiler.hir.hir_types.{HirModule}`.
- The typed-facet admission feature the spec exercises (authenticated manifest
  descriptors as facet seal authority, `E-FACET004`) must land its
  implementation modules first, or the spec must be retired with the feature.

## Unblock condition

Land `driver_facet_manifest_authority` and the `ApkFacet*` aspect-pack types,
or delete the spec together with the feature decision. Leaving it RED documents
the missing subject.

