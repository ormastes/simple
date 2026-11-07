# Rich canonical types in the shared data-schema resolver

Date: 2026-11-07. Status: implementation/test source approved by Astra; execution
pending. This is the next bounded W0/W1 structural package after
[V2 #7561](https://github.com/ormastes/simple/pull/7561), not full W1 completion.
<!-- codex-architecture -->

## Type authority and versioning

The existing language semantic owner must resolve source/config type syntax,
imports, aliases, nested arguments and qualifiers. Its pointer-free
`DataSemanticTypeIdentityV1` codec retains a complete structural descriptor,
explicit version and checked UTF-8 byte length. Exact identity uses the complete
validated descriptor, never a digest, local SymbolId, unqualified name or nominal
placeholder. The separate semantic-type/HIR adapter lane owns that implementation.

V1 `DataTypeRefV1.path/args` keep their flat nominal meaning. V2 remains a
compatible wrapper over that contract. Rich `DataAttrDeclV3` instead carries the
semantic owner's validated identity directly. Its resolved attributes and
`DataSchemaSurfaceV3` are versioned independently, with explicit tree, views,
properties and a V3 outer digest. There is no misleading coarse V2 projection.

Schema digesting uses full structural descriptors and explicit byte-length
prefixes. It distinguishes nested qualifiers and declaring owners, retains
requiredness/defaults/applicability and property meaning, and excludes declaration
order/provenance. The SHA-256 digest identifies the complete schema; it does not
replace exact type comparison.

## One reducer, versioned wrappers

`src/compiler/00.common/data/data_schema_core_v1.spl` owns the internal normalized
declaration/attribute reduction: canonical attribute grouping, exact owner-supplied
type-key equality, requiredness/default conflicts, applicability and provenance.
Its records are implementation facts inside the common owner, not another public
language type system or wire schema.

The V1 wrapper keeps its existing alias/flat conversion, shape/authority checks,
diagnostic ordering, public output and original digest function. The V3 wrapper
validates complete semantic identities before passing canonical keys to the same
private reducer. It reconstructs resolved typed V3 attributes without treating a
canonical descriptor as a V1 nominal path.

`data_schema_property_resolver_v1.spl` owns shared property normalization,
visibility/mutation/accessor checks, explicit views, forwarding checks and the
indexed dependency graph. The existing V2 public helper names are re-exported
from its compatibility wrapper. This avoids copying a second property checker.
The V2 digest function body remains unchanged; its original unit examples remain
applicable. Graph work is O(V+E), while inherited grouping/sorting remains a cold
polynomial operation under the existing input bounds.

## Configuration and consumers

`data_schema_sdn_common_v1.spl` is the one shared syntax-normalization path.
V2's public decoder still accepts its original version and flat `args`, returning
the same V2 records. V3 uses `simple.data-policy/v3`, accepts a full language type
expression in `type`, and refuses `args`. Its public decoder returns explicitly
unbound `DataSchemaUnboundInputV3`/`DataSchemaUnboundAttrV3` records. It never
manufactures a semantic identity from configuration text.

The frontend/config consumer must parse and bind that expression through the
existing semantic owner in its authorized compilation context, then construct
`DataAttrDeclV3` and call `data_schema_resolve_v3(authority, views, decls)`. No alias
table is passed to the rich resolver: language alias expansion is the semantic
owner's responsibility. The consumer freezes one complete successful surface and
uses its outer digest for context/explanation/cache identity. No field access
parses SDN or re-resolves a schema.

Raw type expressions are bounded to 64 KiB before binding. The shared document,
view, attribute, effect, dependency, name and default limits remain in force.
Unknown keys, wrong versions, malformed syntax shapes and duplicate keys fail
without a usable partial surface. A dedicated schema document still does not
grant build authority or implement full project config discovery.

## Evidence and ownership

Implementation owns only canonical common schema reduction/configuration and its
focused tests/docs. The semantic identity codec/HIR adapter, real frontend/config
context, HIR access sites and lifecycle consumers have separate assigned owners.
No StorageLayoutPlanV1, CollectionPlan, `.sprof` authority or trace provider changes.

`data_schema_resolver_compatibility_spec.spl` includes a frozen independent V1
digest fixture, canonical/provenance ordering, validation ordering, exact conflict
text and V2 projection/property expectations. `data_schema_resolver_v3_spec.spl`
uses the semantic codec to test rich identity transport, nominal/qualifier
distinctions, malformed identities, shared forwarding/property rules, V3 digests
and explicitly unbound SDN. These fixtures do not prove HIR alias/import binding;
the separate adapter/consumer lane must supply that executed evidence.

Tests, docgen, maintenance scores, compiler/lib/MCP/LSP checks and native smoke
remain UNEXECUTED without an admitted self-hosted runtime. Static preservation of
digest function bodies and source review are narrower evidence than runtime
compatibility. No whole-feature or full W1 PASS follows from this package.
