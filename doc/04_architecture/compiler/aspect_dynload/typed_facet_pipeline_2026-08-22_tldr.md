<!-- codex-architecture -->
# Typed `facet<T>` Pipeline — TLDR

Typed facets are one cross-layer capsule: frontend declarations, a first-class
`HirExprKind.FacetAcquire`, explicit MIR acquire/invoke/release operations,
passive records in `common.facet_abi`, and one mutable loader-owned
`FacetRuntimeContext`.

- Public results remain `Option<FacetRef<T>>`,
  `Result<Option<FacetRef<T>>, FacetLoadError>`, and
  `Result<FacetRef<T>, FacetLoadError>` for try/load/require respectively.
- Absence is not failure. `try_facet` does no I/O. Ambiguity always fails;
  source, pack, filesystem, and load order never choose a provider.
- `FacetRef<T>` pins one exact generation. Quiescing refuses new pins; final
  unpin releases sidecars, witness storage, and mappings. Stale pins cannot
  touch a replacement generation.
- Interpreter dispatch uses a checked callable ID; native dispatch is owned
  only by `compiler.loader.facet_native_abi` and validates executable extent,
  signature, ABI, and generation before a canonical call facade.
- Schema changes require regenerated visitors/hashes/codecs and cache-version
  bumps. A lossy restore is a release-blocking failure.
- Catalog route/cache identity includes the visible catalog digest. Failed
  activation rolls back fully; only immutable completed generations publish.

Implementation details and exact names:
`doc/04_architecture/compiler/aspect_dynload/typed_facet_pipeline_2026-08-22.md`.
