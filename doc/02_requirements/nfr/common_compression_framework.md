# NFR Requirements — `common_compression_framework`

- NFR-001 Performance: LZ4 round trips for small and medium buffers should complete within normal unit-test budgets on the host interpreter/runtime.
- NFR-002 Reliability: Malformed headers, truncation, and checksum failures must return explicit errors rather than partial success.
- NFR-003 Maintainability: Shared API and per-codec logic must stay separated enough for later compressed-block and SIMD work.
- NFR-004 Portability: The public library remains pure `.spl` and must compile without adding a C/Rust codec dependency.
- NFR-005 Interoperability: First delivery must emit standard Zstd and XZ/LZMA2 containers that host tools can decode for the supported subset.
- NFR-006 Observability: Architecture/design docs must record startup path, dispatch path, state reset rules, and cache/table strategy.
- NFR-007 Safety: Unsupported standard features must fail closed with `UnsupportedFeature`.
