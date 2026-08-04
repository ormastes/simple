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
| facet artifact contract | `compiler/00.common/structural_contracts/facet_artifact.spl`; SHB v1.1 optional facet-contract section and ordinary-SMF `.facet_bindings` Note consumed through existing readers |
| dynamic advice publication | `compiler/99.loader/loader/advice_binding_registry.spl` (catalog-prepared slots, canonical preordered chains, exact-generation publish/unbind, disabled-path counters; no pointcut evaluator or lifecycle ownership) |
| application runtime owner | `app/startup/aspect_application_runtime.spl` (retained trust/cache/coordinator, exact relative routes, mission seal, opaque per-aspect generation leases, quiesce/drain unload) |

The syntax parser is an explicitly feature-scoped frontend surface; it does not
replace the established advice/CE parsers. The activation adapter composes
`DynSmfSession`, `CandidateMapping`, `GenerationState`, and `LifecycleManager`;
it does not own executable relocation or a second module discovery path.
Production activation stages facet and advice candidates only after the module
loader validates witness ownership. Advice targets must occur in the catalog's
prepared-slot set. Both registry publications and lifecycle promotion are
computed before one coordinator value becomes visible. Advice lookup preserves
existing AOP order (priority, specificity, witness name), never re-evaluates
pointcuts, and exposes the non-zero prepared-slot guard through deterministic
counters and a footprint descriptor. The application runtime removes both
facet and advice visibility before unload drain. Mission policy rejects runtime
advice-patch activation.

`advice_dispatch_slot` is the loader-validated production execution seam for
zero-argument `before`, `after_success`, and `after_error` witnesses. Admission
captures the resolved address and owner; dispatch revalidates both against the
existing `ModuleLoader` before invoking any callback, so an invalid chain fails
before partial execution. Runtime `around` is rejected because no dynamic
exactly-once `proceed` continuation exists. With
`CompileOptions.prepared_dynamic_advice`, the established pointcut/weaving authority now
produces stable execution slots and automatic phase-specific
`simple.prepared_advice_dispatch.v1` MIR intrinsics. They remain non-executable
until the lifecycle-safe backend bridge below is complete.

The shared `PreparedAdviceSlotPlan` contract carries schema ID/version, stable
slot ID, target function identity, and admitted before/after forms.
`MirModule.prepared_advice_slots` preserves this table through normal/bootstrap
lowering, AOP/debug reconstruction, MIR optimizers, and VHDL aggregation;
`serialize_mir_prepared_advice_slots` provides deterministic handoff bytes.
The driver collects a deterministic schema-v1 table. The loader derives an
immutable schema-v1 dispatch projection containing exact publication,
generation, witness-owner, and address identity from its canonical registry.
All execution/output surfaces fail closed until projection install is atomic
with publication, invalidation precedes drain, and dispatch pins the exact
generation. Check/interpreter reject the option directly; JIT and every AOT
backend reject produced slots before code generation.

## Ownership boundaries

### Resolver installation dependency

The resolver-installation inversion is closed through
`85.mdsoc/feature/module_loading/app/ModuleResolverDiscoveryPort`.
Its frozen `resolve_inputs(inputs) -> Result<ModuleResolverPort, text>` operation
returns the existing immutable roots/fingerprint contract. The 99-loader aspect
registry adapter implements discovery; production CLI composition injects it
before phase-one collection. Layer 80 imports only the application port and the
shared path policy in layer 00, with no loader implementation dependency.
Compatibility constructors intentionally inject the empty discovery port.

### Prepared dynamic join points

`MirModule` carries deterministic prepared-slot metadata and the explicit
config producer inserts phase-specific prepared-dispatch intrinsics. Catalog
slot strings and the loader projection consume the same finite slot identity;
no runtime pointcut evaluator is introduced.

The remaining implementation owner is the loader/backend bridge: atomically
install the derived projection with canonical publication, invalidate it before
unload drain, and pin/validate its exact generation while a backend trampoline
dispatches. The projection is never an independently mutable registry.

## Cache and invalidation

Validated index keys include catalog generation, pack digest, target, variant fingerprint, runtime ABI, core public ABI hash, and core layout ABI hash. Decoded module keys also include module digest. Catalog/digest/generation/semantic changes invalidate positive and bounded negative entries. Eviction respects module-generation pins and resource refcounts. There is no request-time full-tree scan, repeated source read, or subprocess.

## Compatibility

Existing `on pc{...} use ...`, ordinary SMF v0.1, current dynSMF controls/evidence, and current variant precedence remain compatible. New syntax and dynamic patching are feature-gated. `AspectPackProvider` is introduced only after the byte-backed loader seam is proven.
