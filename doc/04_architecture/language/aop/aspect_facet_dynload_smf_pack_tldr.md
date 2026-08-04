# Aspect Facets + SFM Packs — TL;DR

```sdn
flow:
  build: TypePredicateBytecode -> FacetBindingPlan + prepared advice slots -> AspectCatalog
  package: app.sfm -> aspect/*.sfm -> opaque module.smf
  load: DynSmfSession -> AspectExecutionContext -> staged generation
```

- Dynamic facets expose affine `FacetRef<T>` guards and never change base
  layout/parents. A compiler-generated private typed adapter retains the base
  operand, resolved contract-ordered method table, and exact generation lease.
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
- `CompileOptions.prepared_dynamic_advice` derives execution slots from the existing
  weave authority and emits automatic entry/return/abort MIR dispatch intrinsics.
- `PreparedAdviceSlotPlan` is preserved and deterministically serialized; the
  loader derives an immutable exact-generation projection from its one registry.
- `AspectExecutionContext` solely owns loader/lifecycle/registries/projection.
  The reviewed v2 intrinsic carries that exact typed context. The producer and
  driver validator exist, but ordinary-call rewriting remains fail-closed until
  MIR can propagate the dispatcher's `Result` through arbitrary target returns.
- Residual v1/v2 intrinsics and non-admitted targets remain E-AF010. No backend
  trampoline, process-global handle, or second lease authority is permitted.
- Check/interpreter reject the option directly; JIT and every AOT backend reject
  produced slots through the same centralized admission boundary.
- D4 and D5 compiler/runtime foundations are partially implemented. Executable
  v2 rewriting, source/HIR facet acquisition, semantic affine enforcement, and
  balanced release insertion remain open; verification is `STATUS: FAIL`.
- Resolver startup now crosses `85.mdsoc` through
  `ModuleResolverDiscoveryPort.resolve_inputs`; production composition injects
  the 99-loader adapter, while compatibility/test constructors stay explicitly
  empty. Layer 80 has no loader implementation import.
- Cold aspects open/read/decompress/map/allocate/scan nothing before activation.
