<!-- codex-research -->
# GPU Web and DB Offload Feature Requirements

Status: selected requirements, recovered.

Selected scope: shared web/database GPU batch executor plus full RAM-only,
SSD-backed, and NoSQL/vector database-mode ambition. Reliability first, GPU
performance second.

## Requirements

- `REQ-GPU-WDB-001`: The HTTP server must implement reverse proxy support using existing `ServerConfig.upstreams`, `LocationConfig.proxy_pass`, `UpstreamConfig`, and `UpstreamServer`.
- `REQ-GPU-WDB-002`: Proxy locations must use a worker-level streaming state machine instead of a buffered `ContentHandler` returning one complete `HttpResponseData`.
- `REQ-GPU-WDB-003`: CPU workers must own TCP accept, TLS/HTTP parsing, routing, proxy forwarding, backpressure, timeout handling, and response serialization.
- `REQ-GPU-WDB-004`: Reverse proxy must support nonblocking upstream connect, request serialization, response header/body streaming, slow-client handling, bounded buffers, and explicit errors.
- `REQ-GPU-WDB-005`: Reverse proxy must drop or rewrite hop-by-hop headers and keep WebSocket/upgrade as a separately designed path.
- `REQ-GPU-WDB-006`: Reverse proxy must select upstreams from existing `UpstreamConfig`, starting with round-robin and extension points for least-connections/health checks.
- `REQ-GPU-WDB-007`: Reverse proxy must support upstream connection reuse or pooling.
- `REQ-GPU-WDB-008`: The system must provide a shared bounded GPU batch executor for web and database workloads with explicit CPU fallback.
- `REQ-GPU-WDB-009`: Web GPU offload must be opt-in by route/workload and target coarse-grained payload compute such as inference, embeddings, ranking, vector search, large transforms, image/video, or large compression/encryption batches.
- `REQ-GPU-WDB-010`: Web GPU offload must not move TCP accept, HTTP parsing, routing, normal proxy forwarding, or per-request load balancing to the GPU.
- `REQ-GPU-WDB-011`: Database GPU offload must be operator/planner driven for eligible scan, filter, projection, aggregation, join, vector search, and large transform operators.
- `REQ-GPU-WDB-012`: Database GPU offload must preserve CPU execution as the authoritative compatibility and correctness path.
- `REQ-GPU-WDB-013`: RAM-only DB mode must support GPU-resident or pinned-host column/vector batches for eligible analytical and vector-search operators.
- `REQ-GPU-WDB-014`: RAM-only DB mode must define layout, invalidation, memory pressure, and CPU fallback before speedup claims.
- `REQ-GPU-WDB-015`: SSD-backed GPU DB mode must preserve WAL, checkpoint, reopen/recovery, and invalidation while accelerating only batch-friendly reads/operators.
- `REQ-GPU-WDB-016`: GPUDirect-compatible transfer paths are optional hardware-gated optimizations; correctness must not depend on them.
- `REQ-GPU-WDB-017`: NoSQL/vector GPU DB mode must support vector/document paths for ANN/vector search, batched document filters, embedding search, and large projection/transform batches.
- `REQ-GPU-WDB-018`: NoSQL/vector mode keeps metadata filtering, persistence, durability, replication, and small writes on CPU/storage unless a later design proves otherwise.
- `REQ-GPU-WDB-019`: GPU execution must use bounded batches and explicit completion evidence; per-request GPU dispatch is not the default.
- `REQ-GPU-WDB-020`: DPU, SmartNIC, DOCA GPUNetIO, and full packet/TLS offload are out of current implementation scope.
