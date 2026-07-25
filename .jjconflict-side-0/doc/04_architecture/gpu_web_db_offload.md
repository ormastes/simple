<!-- codex-design -->
# GPU Web and DB Offload Architecture

Status: recovered design draft.

## Decision

Use a CPU-owned HTTP reverse proxy and DB control plane with a bounded shared
GPU batch executor for coarse payload work.

```text
client -> CPU HTTP worker/reverse proxy -> route or DB planner eligibility
       -> bounded GPU batch executor -> CPU response / DB durability path
```

The GPU does not accept TCP, parse HTTP, route requests, own proxy forwarding,
or replace WAL/checkpoint/invalidation control paths.

## Capsules

| Capsule | Owner | Role |
|---------|-------|------|
| Proxy stream | `nogc_async_mut/http_server/worker.spl` | Client/upstream streaming state, buffers, deadlines |
| Upstream pool | HTTP server | Round-robin selection, reuse, fail counters |
| GPU batch executor | shared GPU lane | Bounded admission, fallback, completion evidence |
| Web GPU routes | web/app integration | Route-level coarse compute descriptors |
| DB GPU planner | DB planner | Operator eligibility and generation checks |
| DB mode adapters | database lib | RAM, SSD, and NoSQL/vector mode contracts |

## Proxy Path

`handler_type == "proxy"` branches before buffered handler dispatch. The state
machine is `Connecting -> SendingRequest -> ReceivingHeaders -> StreamingBody
-> Complete/Failed`.

## GPU Path

GPU batches require kind, mode, input generation, max bytes, backend, and CPU
fallback policy. Initial implementation should include a CPU fallback backend
and a deterministic evidence backend before real CUDA/platform execution.

## DB Modes

RAM-only mode admits column/vector batches into GPU-resident or pinned buffers.
SSD-backed mode keeps durability on CPU and accelerates only batch-friendly
reads/operators. NoSQL/vector mode targets ANN/vector search and batched
document/vector filters while metadata and small writes remain CPU/storage.
