# Facet manifest authority must survive to HIR resolution

Status: implemented in the typed-facet lane; pending aspect-runtime integration and verification.

`resolve_methods(module, authority)` and `MethodResolver.resolve_module(module, authority)` now
accept `ManifestSealAuthority?`. A module containing any facet declaration requires `Some(authority)`;
ordinary modules pass `nil`. The compiler must not derive this value from source HIR.

The pack-admission owner must construct the authority only after authenticating the manifest and
descriptor. It must carry the admitted `aspect_id`, `aspect_version`, `descriptor_digest`, module ID,
symbol-to-canonical-type map, canonical-type map, provider identity per implementation symbol,
base public-ABI hash, base layout hash, and inspect-capability decision. `SourceFile.facet_manifest`
now retains that admitted descriptor through streaming reconstruction, low-memory eviction, and HIR
reparse. The driver binds its canonical names onto process-local HIR symbols, corroborates the
canonical descriptor digest, and passes the resulting authority to resolution. Canonical
`hir_module.name`, rather than a streaming dictionary alias, selects the owning source.

Remaining integration gate: consume the aspect-runtime ABI-v3 descriptor/digest API, regenerate the
HIR schema artifacts, and run the focused compiler verification. No fallback constructor from
`HirModule`, source aspect declarations, paths, or process state is permitted.
