<!-- codex-research -->

# UTF-8 and Internationalized Text Architecture NFRs

- NFR-001 Correctness: every new or materially changed owned text/i18n/rendering module shall reach 100% measured branch coverage. Reviewed unreachable defensive branches are excluded with proof; they are not counted as covered. Vendor code is excluded unless modified.
- NFR-002 Conformance: official Unicode 17.0.0 normalization, segmentation, BiDi, line-break, identifier, and security data applicable to the implemented capability shall pass without locally weakened vectors.
- NFR-003 Streaming: every partition of short encoded inputs and every bounded-output cutoff shall match whole-buffer reference results, including progress and first-error location.
- NFR-004 ASCII: compiler wall time and lex-only throughput shall not regress beyond 1% and 2% respectively on matched retained baselines; any larger change requires a reviewed tradeoff and blocker record.
- NFR-005 Memory: production transcoding shall not allocate an O(scalar-count) intermediate; plain traversal shall allocate no index; parser allocated bytes and peak RSS shall not regress beyond 2%; noalloc profiles shall perform zero heap allocation after initialization.
- NFR-006 Capability cost: i18n-disabled and tiny builds shall contain no unused catalog registry, locale branch, Unicode table, shaping backend, atlas backend, or renderer data beyond selected capabilities.
- NFR-007 Construction: hot construction and formatting shall be single-pass or amortized-linear through `TextSink`; repeated immutable concatenation and per-argument whole-message replacement are prohibited.
- NFR-008 Indexing: sparse index memory shall be proportional to checkpoints, not scalar count; ASCII text shall not allocate an index; stride/threshold decisions require measured latency and bytes/source-byte evidence.
- NFR-009 Rendering correctness: each promoted GPU row shall prove emission, compilation, submission, fence/device completion, device-origin readback, and CPU-oracle pixel/hash parity for the exact shaped payload and configuration.
- NFR-010 Rendering performance: retained 2D and 3D rows shall record shape, layout, material preparation, atlas lookup/upload, queue-device completion, fence observation, readback, frame p50/p95, allocations, RSS, fallback state, viewport, corpus, backend, and revision.
- NFR-011 Scalability: benchmark sizes shall span 0 bytes through 64 MiB and include boundary sizes around scalar/SIMD/buffer thresholds; rendering corpora shall span empty, short UI, paragraphs, dense HUD, world labels, long combining sequences, and atlas churn.
- NFR-012 Determinism: generators, catalogs, IDs, benchmarks, fixtures, and evidence manifests shall record versions/hashes and produce stable output under identical inputs.
- NFR-013 Safety: malformed input, overflow, recursion, output expansion, stale handles/generations, unsupported CTM/modes, cache mutation on rejection, catalog corruption, and device fallback shall fail closed.
- NFR-014 Portability: scalar evidence is mandatory everywhere; compiled x86, AArch64, RISC-V, CPU, Vulkan, CUDA, Metal, and other selected backend rows require forced-backend evidence; unavailable native rows remain open blockers.
- NFR-015 Observability: perf-sensitive paths shall expose level-gated counters/timings for bytes, scalars, clusters, glyphs, runs, cache hit/miss, atlas bytes, allocations, fallback, backend, and failure reason without default hot-path logging.
- NFR-016 Test honesty: planned tests, source review, synthetic handles, CPU mirrors, emulator output, screenshots, and fallback pixels shall not be promoted to native execution or device-readback PASS.
