# Aspect Facet Feature Requirements — TL;DR

```sdn
required:
  semantics: FacetRef<T> + TypePredicateBytecode
  package: AspectCatalog + AspectPackDirectory in SFM
  provider: AspectPackProvider -> ObjectProvider
  lifecycle: atomic existing-generation publication
```

- No core dependency or base-layout mutation.
- Resolver owns deterministic relative roots; runtime performs no search.
- Opaque SMF chunks load selectively from SFM.
- Validation fails before publication.
- V1 uses public contracts/owner capabilities.
- Existing compile-time AOP remains authoritative.

