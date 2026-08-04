# Aspect Facets + SFM Packs — TL;DR

```sdn
flow:
  build: TypePredicateBytecode -> FacetBindingPlan + prepared advice slots -> AspectCatalog
  package: app.sfm -> aspect/*.sfm -> opaque module.smf
  load: DynSmfSession -> AspectPackProvider -> ObjectProvider -> staged generation
```

- Dynamic facets expose `FacetRef<T>` and never change base layout/parents.
- V1 uses public contracts or owner-exported capability facades only.
- Existing compile-time AOP remains authoritative and exactly ordered.
- Loader advice chains bind only catalog-prepared slots and keep canonical
  priority/specificity/witness ordering; runtime never re-matches pointcuts.
- `advice_dispatch_slot` revalidates loader owner/address before zero-argument
  before/after calls; dynamic `around` is denied without a real `proceed` path.
- Variants resolve at build time; runtime never traverses `variants/`.
- SFM owns pack/catalog/index/compression/signatures; SMF stays opaque.
- Existing dynSMF, loader, cache, and resource-lifecycle owners are extended.
- Activation stages all dependencies then publishes one generation atomically.
- Facet/advice visibility is removed before lifecycle drain; mission policy
  rejects runtime advice patching.
- Disabled prepared slots have an explicit non-zero guard footprint and expose
  lookup/hit/miss/check/branch counters to the retained NFR harness.
- Automatic MIR prepared-slot callers remain open; explicit app-runtime dispatch
  does not by itself prove business-path patchpoint integration.
- `PreparedAdviceSlotPlan` is preserved and deterministically serialized in MIR,
  but non-empty driver emission fails closed until a real backend table/caller exists.
- Prepared-slot metadata/guards are not yet emitted by MIR: `50.mir` is the
  next producer owner, `70.backend` lowers them, and loader/app remain consumers.
- Resolver startup now crosses `85.mdsoc` through
  `ModuleResolverDiscoveryPort.resolve_inputs`; production composition injects
  the 99-loader adapter, while compatibility/test constructors stay explicitly
  empty. Layer 80 has no loader implementation import.
- Cold aspects open/read/decompress/map/allocate/scan nothing before activation.
