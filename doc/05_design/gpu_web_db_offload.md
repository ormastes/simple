<!-- codex-design -->
# GPU Web and DB Offload Detail Design

Status: recovered design draft.

## Proxy State

```simple
enum ProxyState:
    Connecting
    SendingRequest
    ReceivingHeaders
    StreamingBody
    Complete
    Failed(reason: text)

class ProxyConnection:
    client_fd: i64
    upstream_fd: i64
    state: ProxyState
    upstream_name: text
    upstream_addr: text
    request_head: [u8]
    client_to_upstream_buffer: [u8]
    upstream_to_client_buffer: [u8]
    connect_deadline_ms: i64
    read_deadline_ms: i64
    write_deadline_ms: i64
```

Reserve worker op constants `OP_PROXY_CONNECT = 20`,
`OP_PROXY_SEND_REQUEST = 21`, `OP_PROXY_RECV_RESPONSE = 22`, and
`OP_PROXY_SEND_CLIENT = 23`.

## GPU Batch Descriptor

```simple
enum GpuBatchKind:
    WebInference
    WebEmbedding
    WebRank
    WebTransform
    DbScanFilterProject
    DbJoinAggregate
    DbVectorSearch
    DbDocumentFilter

class GpuBatchDescriptor:
    kind: GpuBatchKind
    mode: text
    input_generation: i64
    max_batch_bytes: i64
    preferred_backend: text
    fallback_required: bool
```

Submission returns `Result<GpuBatchTicket, GpuBatchError>`. Queue-full,
unsupported backend, stale generation, transfer failure, and kernel failure are
explicit fallback reasons.

## Reliability Order

1. CPU reverse proxy correctness.
2. CPU DB correctness and invalidation.
3. Bounded resource controls.
4. GPU fallback discrimination.
5. GPU performance evidence.
