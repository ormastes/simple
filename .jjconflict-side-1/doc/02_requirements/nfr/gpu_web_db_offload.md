<!-- codex-research -->
# GPU Web and DB Offload NFR Requirements

Status: selected requirements, recovered.

## Reliability First

- `NFR-GPU-WDB-001`: GPU support must be optional; CPU paths must pass on hosts without compatible GPUs.
- `NFR-GPU-WDB-002`: CPU execution is authoritative for correctness on all GPU-eligible web and database work.
- `NFR-GPU-WDB-003`: GPU absence, queue saturation, transfer failure, kernel failure, or unsupported operators must produce observable fallback or explicit error.
- `NFR-GPU-WDB-004`: Proxy reliability includes connect/read/write/client timeouts, slow-client handling, bounded buffers, and backend error propagation.
- `NFR-GPU-WDB-005`: DB reliability preserves WAL, checkpoint, reopen/recovery, index invalidation, cache invalidation, and query correctness across CPU/GPU execution.
- `NFR-GPU-WDB-006`: RAM-only GPU DB mode handles GPU memory pressure with bounded admission and no silent data loss.
- `NFR-GPU-WDB-007`: SSD-backed GPU DB mode proves cold, warm, and post-reopen behavior for accelerated operators.
- `NFR-GPU-WDB-008`: NoSQL/vector GPU mode proves metadata filters, vector results, and CPU fallback return the same logical results on oracle datasets.
- `NFR-GPU-WDB-009`: The implementation exposes bounded controls for pinned memory, GPU queue depth, per-route/query batch bytes, proxy buffers, upstream pool size, and RSS.
- `NFR-GPU-WDB-010`: Production performance evidence must use cached/native compiled artifacts where available and must not present interpreter-only throughput as production throughput.

## GPU Performance After Reliability

- `NFR-GPU-WDB-011`: Native full async HTTP/proxy baseline must be measured before GPU throughput claims.
- `NFR-GPU-WDB-012`: Reverse proxy benchmarks report throughput, p50/p95/p99, max RSS, upstream reuse, timeout counts, and error counts.
- `NFR-GPU-WDB-013`: GPU evidence reports GPU hits, CPU fallbacks, fallback reasons, queue depth, batch size, transfer bytes, kernel time, and completion latency.
- `NFR-GPU-WDB-014`: RAM-only DB mode benchmarks measure eligible scan/filter/project and vector-search throughput against CPU baseline.
- `NFR-GPU-WDB-015`: SSD-backed GPU DB benchmarks measure large sequential batch scans, persisted vector search, WAL/reopen overhead, and cold/warm cache behavior.
- `NFR-GPU-WDB-016`: NoSQL/vector mode benchmarks measure vector index build/search, batched document filters, metadata-filter fallback, and high-recall behavior.
- `NFR-GPU-WDB-017`: GPU performance claims are rejected for tiny batches where transfer and launch overhead dominate.
- `NFR-GPU-WDB-018`: Benchmark reports include dataset size, row/document count, vector dimensions, index type, storage provider, backend, fallback policy, and hardware.
- `NFR-GPU-WDB-019`: SPipe specs assert both CPU fallback and GPU-hit states; no placeholder passes or equality-only GPU claims.
- `NFR-GPU-WDB-020`: Every requirement in the GPU-WDB family traces to design, implementation, and evidence before release.
