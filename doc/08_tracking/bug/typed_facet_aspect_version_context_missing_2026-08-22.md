# Typed facet parser lacks authoritative aspect-version context

## Status

Open integration dependency. Typed facet declarations fail closed when the
parser has no positive manifest-derived aspect version.

## Evidence

The immutable loader API `pack_snapshot_index_view` in
`src/compiler/99.loader/pack_file_snapshot.spl` exposes an authenticated APK
index view without reopening the pack. The current APK directory records an
`aspect_id`, module ABI/layout hashes, and variant fingerprint, but it does not
serialize the aspect version required by `ParserFacet*` and `HirFacet*`.

Consequently no authoritative source-path/module lookup can currently provide
`(aspect_id, aspect_version)` to `parser_set_aspect_context`. The parser must
not default the version to 1 or infer it from a module ID.

## Required fix

1. Add the declared aspect version to the manifest-owned APK directory schema,
   producer, checked parser, digest coverage, and compatibility version.
2. Expose an immutable lookup from admitted snapshot/module identity to
   `(aspect_id, aspect_version)` using the existing snapshot index owner.
3. Have driver parse setup call `parser_set_aspect_context` before parsing an
   aspect module and clear it after that parse.
4. Add a negative control proving an absent or unauthenticated version remains
   a fatal typed-facet parse diagnostic.

No direct filesystem read or second manifest parser is permitted on the
frontend parse path.

## Remaining semantic authority dependency

Pack admission can now truthfully supply `aspect_id`, positive
`aspect_version`, `module_id`, and the digest-authenticated immutable pack
extent as `descriptor_digest`. It cannot truthfully construct the rest of
`ManifestSealAuthority`: the APK directory does not authenticate
`type_name_by_symbol`, `type_by_name`, `provider_by_impl_symbol`,
`base_public_abi_by_impl_symbol`, `base_layout_by_impl_symbol`, or
`inspect_capability_by_impl_symbol`.

HIR sealing must therefore fail closed until a versioned authenticated
manifest descriptor carries those maps and the driver binds them to the
admitted snapshot. Source-declared binding/provider text and HIR-derived maps
are not substitutes for manifest authority.

## Schema-v3 consumer handoff

`ApkFacetManifestDescriptorV1` is the frozen producer model. Schema 3 appends,
after each positive `aspect_version`, a length-prefixed lowercase SHA-256 of
the canonical descriptor followed by its length-prefixed canonical bytes.
Those bytes contain, in order: authority/signature-receipt identity, sorted
concrete types, sorted interfaces, sorted `(interface_id, method_name)`
methods, and sorted implementations. Implementations bind provider identity,
implementation/base ABI/layout hashes, inspect capability, and sidecar
kind/ABI. The producer rejects empty identities, malformed hashes,
noncanonical order, duplicate keys/IDs, inspect-without-layout, and incomplete
sidecar pairs.

The snapshot/index owner must decode schema 3 from its existing immutable
digest-verified directory view, recompute the descriptor digest, repeat the
same canonical-order/collision validation, and publish a read-only descriptor
record beside `PackAspectModuleIdentity`. Schema 1/2 remain loadable for
non-facet compatibility but must return `APKIDX_FACET_DESCRIPTOR_MISSING` when
semantic authority is requested.

The HIR driver constructs `ManifestSealAuthority` only after matching HIR
symbols to authenticated canonical type/implementation names. This matching
creates process-local dictionary keys; every dictionary value comes from the
verified descriptor. Missing, duplicate, or unmatched names fail closed. The
driver must never take provider IDs, concrete/interface/method IDs, ABI/layout
hashes, capability, or sidecar facts from source declarations or recompute
them from HIR as a substitute.
