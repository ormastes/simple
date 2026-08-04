# Aspect Facet Agent Tasks — TL;DR

```sdn
order:
  parallel_1: [type_predicates, sfm_pack_codec, resolver_roots]
  parallel_2: [facet_semantics, loader_adapter]
  integrate: catalog_lifecycle
```

- Shared interfaces, steps, and helper names are frozen before fan-out.
- Agents own non-overlapping paths.
- Root Codex is merge owner, manual reviewer, and final reviewer.
- Placeholders fail explicitly.
- Focused gates run per lane; broad verification runs once after integration.

