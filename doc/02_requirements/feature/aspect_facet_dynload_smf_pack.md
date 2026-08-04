# Aspect Facets and Demand-Loaded SFM Packs — Feature Requirements

**Selection record:** The user selected the referenced design with the explicit condition that it be updated to current Simple design and principles. This selects the SFM outer-container/current-owner option and rejects a parallel SMF pack format or duplicate lifecycle registry.

## Requirements

- **REQ-AF-001 — Core independence and layout stability.** An optional aspect must introduce no core-to-aspect dependency and must not change a dynamic target object’s base layout, nominal parents, or mandatory ABI.
- **REQ-AF-002 — Typed explicit acquisition.** Optional behavior is accessed through `FacetRef<T>` using no-I/O lookup, policy-aware optional acquisition, or required acquisition APIs with typed failure.
- **REQ-AF-003 — Structural selection.** `FacetBindingPlan` uses one shared `TypePredicateBytecode` representation for deterministic `type`, `implements`, and `subtype` selectors. Static discovery and later type registration must yield the same binding result in either registration order.
- **REQ-AF-004 — Resolver-owned aspect roots.** Aspect source roots are manifest-relative, canonicalized, escape-checked, collision-checked, and resolved at build time. Runtime performs no source-root, directory, or `variants/` search.
- **REQ-AF-005 — SFM aspect pack.** `AspectPackDirectory` is outer SFM metadata indexing opaque ordinary SMF module payloads or explicit co-load clusters. Each payload is independently framed, bounded, hashed, and selectively readable without decompressing unrelated entries.
- **REQ-AF-006 — Deterministic application catalog.** `AspectCatalog` records concrete build-resolved module IDs, pack-relative locations, digests, target/runtime ABI, variant fingerprint, dependencies, activation policy, and binding summaries. `AspectPackProvider` supplies selected SMF bytes through the existing object-provider/SMF-reader seam.
- **REQ-AF-007 — Fail-closed validation.** Invalid paths, roots, indexes, bounds, decoded sizes, hashes/signatures, target/runtime ABI, variant fingerprints, dependencies, cycles, capabilities, or policies fail before publication and leave the previous generation unchanged.
- **REQ-AF-008 — Atomic lifecycle integration.** Loading, relocation, facet witnesses, optional advice plans, and resources stage under existing loader/dynSMF generation ownership and publish once. Concurrent requests share one transaction; unload respects generation pins and resource refcounts.
- **REQ-AF-009 — Public capability boundary.** V1 facet implementations use public business contracts or explicit owner-exported capability facades. Arbitrary private-layout inspection/mutation is not part of V1.
- **REQ-AF-010 — Existing AOP preservation.** Existing `on pc{...} use ...` semantics, deterministic order, and compile-time weaving remain authoritative. New facet grammar and dynamic modes are proposed, feature-gated additions, not replacements.

## Traceability

| Requirement | Primary executable evidence |
|---|---|
| REQ-AF-001..003, REQ-AF-009..010 | `test/03_system/feature/language/aop/aspect_facet_static_binding_spec.spl` |
| REQ-AF-004 | `test/03_system/compiler/module_resolver/relative_aspect_roots_spec.spl` |
| REQ-AF-005, REQ-AF-007 | `test/03_system/stdlib/dynload/aspect_pack_selective_loading_spec.spl` |
| REQ-AF-003, REQ-AF-006..008 | `test/03_system/app/simple/aspect_catalog_activation_spec.spl` |

