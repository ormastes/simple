<!-- codex-research -->
# GPU Web and DB Offload Domain Research

Status: recovered research summary.

## Findings

- Production reverse proxies such as NGINX, HAProxy, and Envoy keep HTTP/TLS,
  routing, connection pooling, health checks, and filtering on CPU.
- CUDA streams queue GPU kernels and memory copies; they are not TCP accept or
  HTTP request queues.
- Pinned host memory and CUDA streams fit bounded coarse-grained batches, but
  pinned memory must be budgeted.
- GPUDirect RDMA and GPUDirect Storage reduce copies on compatible hardware but
  do not make the GPU a general HTTP/TCP server.
- GPU database prior art accelerates columnar scans, joins, aggregations,
  vector search, and analytical operators. OLTP, durability, small writes, and
  metadata control remain CPU/storage work.
- Spark/RAPIDS is the right pattern: an accelerator plugin replaces supported
  operators and falls back or fails by policy for unsupported ones.

## Direction

Implement CPU reverse proxy and DB control plane first, then a shared bounded
GPU batch executor for coarse web/database operators with explicit CPU fallback.
