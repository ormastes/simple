# Aspect Facet / Dynload Pack Design — TL;DR

```sdn
design:
  semantics: base_object -> FacetRef<T> -> witness
  selection: TypePredicateBytecode(type, implements, subtype)
  deployment: app.sfm -> aspect_pack.sfm -> opaque modules.smf
  activation: DynSmfSession -> staged loader -> atomic generation
```

- The original “SMF pack” is corrected to an SFM aspect pack.
- Dynamic facets are explicit optional views; base layout and nominal ABI stay stable.
- V1 forbids arbitrary private-layout/mutating aspect access.
- Existing AOP and variant resolver remain authoritative; new syntax is feature-gated.
- SFM owns indexes, independent zstd frames, signatures, and catalogs.
- Existing object provider, loader, dynSMF, cache, and lifecycle are extended.
- Cold aspects do no pack I/O/decompression/mapping/allocation before activation.
- Patchable advice has measurable non-zero dormant footprint.
- Facet metadata emission fails closed until a canonical witness symbol is
  genuinely exported; declaration-only method signatures are not executable.
- `advice_dispatch_slot` supports validated zero-argument before/after calls;
  dynamic `around` remains denied without an exactly-once `proceed` path.
- Automatic prepared-slot MIR/backend emission and the final `85.mdsoc`
  resolver-port injection remain release blockers.
