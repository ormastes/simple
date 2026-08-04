# Aspect Facet System Tests — TL;DR

```sdn
specs:
  static: facet binding + predicates
  resolver: relative aspect roots
  pack: selective SFM payload loading
  activation: catalog + atomic generation
```

- Five frozen visible steps define the operator flow.
- Three frozen helpers hide setup/check mechanics.
- Every REQ-AF requirement maps to one or more specs.
- Manifests use dynamic counts, never absolute evidence indexes.
- Failure, cold-counter, and concurrency oracles fail closed.
- Generated manuals mirror executable tests and contain zero stubs.

