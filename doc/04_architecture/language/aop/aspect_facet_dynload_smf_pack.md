<!-- codex-design -->
# Architecture: Aspect Facets and Demand-Loaded SFM Packs

## Decision

Optional facet semantics are a structural extension of existing compile-time AOP, while deployment is an SFM capsule concern. The architecture adds no parallel SMF format, module loader, dynSMF lifecycle, variant resolver, or raw runtime I/O path.

```sdn
architecture:
  build:
    syntax: compiler.10_frontend
    coherence: compiler.20_35_semantics
    predicate: compiler.00_common.TypePredicateBytecode
    weave: compiler.50_mir + compiler.85_mdsoc
    package: compiler.80_driver -> std.sfm
  runtime:
    catalog: application_sfm.AspectCatalog
    provider: loader.ObjectProvider <- AspectPackProvider
    payload: opaque_ordinary_smf
    lifecycle: DynSmfSession + loader_generation
    publication: one_atomic_generation
```

## Invariants

1. Core is complete without optional aspect declarations.
2. Dynamic facets do not alter base layout or nominal parents.
3. `FacetRef<T>` is the only optional typed view.
4. V1 aspects use public contracts or explicit owner capability facades.
5. Variants resolve during build; runtime sees concrete IDs and a fingerprint.
6. SFM owns catalog, directory, compression, signatures, and pack policy; SMF remains an opaque executable code unit.
7. One staged transaction validates every dependency/resource before publishing one generation.
8. Cold catalog entries trigger no pack open, payload read/decompression, mapping, allocation, scan, or config parse.

## Owner boundaries

| Layer/owner | Responsibility | Forbidden coupling |
|---|---|---|
| `compiler/00.common/structural_contracts` | Immutable IDs and `TypePredicateBytecode` shared by frontend/HIR/MIR/loader | No parser, resolver, loader, or runtime implementation logic |
| `compiler/10.frontend` | Proposed facet syntax and selector parsing | No binding coherence or I/O |
| `compiler/20.hir` + type/semantic layers | Contract resolution, descriptor projection, completeness, uniqueness, dependency/access checks | No pack reading or runtime registry mutation |
| `compiler/50.mir`, `85.mdsoc` | Static binding/weaving and dynamic operation schema | No duplicate pointcut evaluator |
| `compiler/80.driver` | Build orchestration and catalog/pack inputs | No new container codec |
| `std.sfm` | Versioned outer manifest, aspect directory, framed payload validation | No SMF symbol/relocation interpretation |
| `compiler/99.loader` | Object-provider adaptation plus reusable staged-loading, publication, and bounded-cache mechanisms | No application policy, source-root, or variant reevaluation |
| `os/smf` | dynSMF policy, status/evidence, activation generation, unload/reload | No second module loader |
| `app/startup` | Owns the process `AspectCatalog`, trust policy, canonical provider-cache instance, activation coordinator, and startup-to-operational seal | No raw `rt_*`, pack codec, module loader, cache implementation, or lifecycle registry |

## Core patterns

- **Typed witness adapter:** `FacetRef<T>` delegates through a `FacetBindingPlan` witness without changing the base object.
- **Feature transform:** type selectors compile once to `TypePredicateBytecode`, then evaluate against closed-world or newly registered descriptors.
- **Provider adapter:** `AspectPackProvider` supplies selected SMF bytes through `ObjectProvider`/`SmfReaderMemory`.
- **Transactional generation:** mapping, relocation, witnesses, advice, and resources stage privately, then publish once.
- **Virtual capsule:** one aspect may span contracts, binding, implementation, tooling, and tests while each leaf consumes only owner facades.

## Implemented owner map

| Owner | Current implementation surface |
|---|---|
| shared predicate contract | `compiler/00.common/predicate.spl`, `structural_contracts/aop.spl` |
| proposed facet syntax/HIR | `compiler/10.frontend/facet_static.spl`, `compiler/20.hir/facet_static.spl` |
| closed-world coherence | `compiler/35.semantics/facet_coherence.spl` |
| typed acquisition | `std.aop.facet` |
| build-time aspect roots | `compiler/99.loader/module_resolver/var_resolution.spl` |
| outer pack codec | `std.sfm.aspect_pack` (`SFM2`; opaque SMF frames) |
| existing-reader adapter | `compiler/99.loader/loader/aspect_pack_provider.spl` |
| catalog and generation adapter | `compiler/99.loader/loader/aspect_catalog.spl`, `aspect_activation.spl` |
| dynamic facet publication | `compiler/99.loader/loader/facet_binding_registry.spl` (validated candidates, exact `activation_key@generation` publication, concrete/open-world lookup, exact unbind; no lifecycle ownership) |
| application runtime owner | `app/startup/aspect_application_runtime.spl` (retained trust/cache/coordinator, exact relative routes, mission seal, opaque per-aspect generation leases, quiesce/drain unload) |

The syntax parser is an explicitly feature-scoped frontend surface; it does not
replace the established advice/CE parsers. The activation adapter composes
`DynSmfSession`, `CandidateMapping`, `GenerationState`, and `LifecycleManager`;
it does not own executable relocation or a second module discovery path.
Production activation stages facet candidates only after the module loader
validates witness ownership. Registry publication and lifecycle promotion are
computed before one coordinator value becomes visible. The application runtime
resolves and pins an exact binding generation in one first-use operation, then
removes that generation's binding visibility before unload drain.

## Cache and invalidation

Validated index keys include catalog generation, pack digest, target, variant fingerprint, runtime ABI, core public ABI hash, and core layout ABI hash. Decoded module keys also include module digest. Catalog/digest/generation/semantic changes invalidate positive and bounded negative entries. Eviction respects module-generation pins and resource refcounts. There is no request-time full-tree scan, repeated source read, or subprocess.

## Compatibility

Existing `on pc{...} use ...`, ordinary SMF v0.1, current dynSMF controls/evidence, and current variant precedence remain compatible. New syntax and dynamic patching are feature-gated. `AspectPackProvider` is introduced only after the byte-backed loader seam is proven.
