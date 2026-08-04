# Aspect Facets + SFM Packs — TL;DR

```sdn
flow:
  build: TypePredicateBytecode -> FacetBindingPlan -> AspectCatalog
  package: app.sfm -> aspect/*.sfm -> opaque module.smf
  load: DynSmfSession -> AspectPackProvider -> ObjectProvider -> staged generation
```

- Dynamic facets expose `FacetRef<T>` and never change base layout/parents.
- V1 uses public contracts or owner-exported capability facades only.
- Existing compile-time AOP remains authoritative and exactly ordered.
- Variants resolve at build time; runtime never traverses `variants/`.
- SFM owns pack/catalog/index/compression/signatures; SMF stays opaque.
- Existing dynSMF, loader, cache, and resource-lifecycle owners are extended.
- Activation stages all dependencies then publishes one generation atomically.
- Cold aspects open/read/decompress/map/allocate/scan nothing before activation.

