# Reverse Proxy GPU Boundary Research

Date: 2026-06-16

## Scope

This note defines the production boundary for reverse proxy and GPU offload work
in `ormastes/simple`.

The reliable architecture is:

```text
client
  -> CPU HTTP server / reverse proxy
  -> optional coarse GPU job queue for GPU-worthy payload work
  -> backend app / inference worker / static file path
```

The rejected architecture is:

```text
client -> GPU accepts TCP/HTTP -> GPU parses/routes/proxies requests
```

CUDA streams are ordered queues for host-launched GPU work such as async memory
copies and kernels. They are not TCP accept queues, HTTP parser queues, or
general web-server event loops. Normal CUDA applications still start on the CPU;
host code owns socket accept, HTTP parsing, routing, auth, validation, and
response serialization.

## Repo State

The repo already has the configuration model needed for reverse proxying:

- `ServerConfig.upstreams`
- `LocationConfig.proxy_pass`
- `UpstreamConfig`
- `UpstreamServer`
- load-balancing strategy fields

The parser already reads `proxy_pass` and upstream server definitions. The
implementation should extend the existing model instead of inventing another
configuration surface.

Target config shape:

```yaml
server:
  listen: "0.0.0.0:8080"
  worker_count: 0
  max_connections: 10000

  locations:
    - pattern: "/api/"
      match: prefix
      handler: proxy
      proxy_pass: "backend"

    - pattern: "/"
      match: prefix
      handler: static
      root: "./public"

  upstreams:
    - name: "backend"
      strategy: round_robin
      servers:
        - addr: "127.0.0.1:3000"
          weight: 1
        - addr: "127.0.0.1:3001"
          weight: 1
```

## Implementation Direction

Reverse proxy must be a worker-level streaming state machine, not a synchronous
`ContentHandler` that returns one fully buffered `HttpResponseData`.

The worker owns the event loop, `IoDriver`, listener socket, connection maps,
router, middleware pipeline, and accepted nonblocking sockets. Proxying belongs
there:

```text
client fd
  -> parse request
  -> route location
  -> if handler_type == "proxy":
       choose upstream
       nonblocking connect
       serialize request with rewritten headers
       stream upstream response headers/body back to client
```

Current reliability evidence:

```text
sh scripts/check/check-httpserver-live-static.shs
STATUS: PASS HttpServer live static

sh scripts/check/check-proxy-live-httpserver.shs
STATUS: PASS proxy live HttpServer reverse proxy

sh scripts/check/check-proxy-live-httpserver-pool.shs
STATUS: PASS proxy live HttpServer upstream pool reuse

sh scripts/check/check-proxy-live-httpserver-reliable-suite.shs
STATUS: PASS proxy live HttpServer reliable suite
```

The live proxy gate now has static serving, fresh-connect proxy correctness,
upstream-pool reuse, upload streaming, and Upgrade/WebSocket tunnel evidence in
one aggregate wrapper. The pool release path keeps reusable backend fds alive
and closes only the client fd after response completion. The tunnel path keeps
HTTP validation/control on CPU, then relays raw post-handshake bytes in both
directions.

## GPU Boundary

Good GPU candidates:

- ML inference
- embeddings
- image/video transforms
- large compression or crypto batches
- vector search
- columnar transforms
- batch scoring/ranking

Bad GPU candidates:

- `accept()`
- epoll/io_uring polling
- TCP state management
- HTTP header parsing
- routing small requests
- per-request load balancing
- normal byte forwarding

The GPU queue boundary should be application-level:

```text
HTTP request
  -> parsed CPU task
  -> GPU queue item
  -> GPU result
  -> HTTP response
```

For GPU throughput, use reusable coarse-grained library surfaces:

```text
per-worker request ring
  -> pinned host batch buffer
  -> cudaMemcpyAsync or backend equivalent
  -> CUDA stream / ProcessingIR backend queue
  -> kernel/model
  -> completion event
  -> CPU response serialization
```

GPUDirect RDMA and GPUDirect Storage can reduce CPU bounce-buffer copies on
supported hardware, but they do not make the GPU a full TCP/HTTP server. The
control path still belongs to CPU, NIC/DPU firmware, kernel drivers, or
userspace networking code. Full network/security/storage offload is a DPU or
SmartNIC topic, not ordinary GPU reverse proxying.

## Production Order

1. Keep native `HttpServer` static and live reverse-proxy gates green.
2. Keep native-safe upstream connection pooling and live pooling evidence green.
3. Add proxy timeouts, max buffered bytes, slow-client backpressure, and
   hop-by-hop header enforcement.
4. Add load-balancing strategies from existing `UpstreamConfig`.
5. Use GPU offload behind selected web/db routes only.
6. Reuse common GPU batch queue/library primitives across web, DB, vector,
   NoSQL, and inference paths.
7. Add RAM-only DB, SSD-backed GPU-accelerated DB, and NoSQL/vector GPU modes
   behind explicit storage/offload profiles.

## Production-Grade Implementation Delta

A complete production implementation is more than the current happy-path proxy
fixture. The reliable-first delta is:

1. Worker event-loop contract:
   - every submitted driver operation has stable owner fd, I/O fd, and op kind
     metadata until completion is consumed.
   - unknown completions are never treated as accepted client sockets.
   - request-body recv/send completion cannot lose `OP_PROXY_RECV_CLIENT_BODY`
     or `OP_PROXY_SEND_REQUEST_BODY` ownership under native builds.
2. Streaming proxy:
   - fixed `Content-Length` uploads stream to upstream without buffering the
     full request.
   - chunked uploads preserve framing unless an explicit dechunk/rechunk mode is
     implemented.
   - upstream response headers/body stream back with slow-client backpressure.
   - WebSocket and CONNECT paths are explicit tunnel states, not buffered
     handlers.
3. Reliability controls:
   - connect, header, body-read, body-write, idle, and pool timeouts.
   - bounded per-connection buffered bytes for client and upstream sides.
   - deterministic close/release paths for client fd, upstream fd, pool entry,
     and pending driver ops.
   - hop-by-hop headers are stripped or handled explicitly:
     `Connection`, `Keep-Alive`, `Proxy-Authenticate`,
     `Proxy-Authorization`, `TE`, `Trailer`, `Transfer-Encoding`, and
     `Upgrade` outside tunnel paths.
4. Load balancing and health:
   - round-robin from `UpstreamConfig` first.
   - least-connections after active-count accounting is reliable.
   - health probes and passive failure marking before production traffic uses
     more than one backend.
5. Evidence:
   - native live static, proxy, pool, fixed-upload, chunked-upload, timeout, and
     slow-client gates.
   - no executable `.spl` specs under `doc/06_spec`.
   - no temporary debug markers or process leaks from evidence wrappers.

Only after those gates are green should GPU performance work be treated as
production work. The reusable GPU library delta is:

1. Common offload API:
   - route/profile declares whether a task is CPU, GPU-preferred, or
     GPU-required.
   - CPU fallback is always available for correctness and unsupported hardware.
2. Batch scheduler:
   - per-worker ring to shared pinned host batch buffers.
   - bounded queue depth, cancellation, deadlines, and backpressure into HTTP
     responses.
   - completion events map back to request/task ids without blocking the event
     loop.
3. Backend adapters:
   - ProcessingIR/CUDA/Vulkan/CPU backend interface reused by web inference,
     DB scans/joins/aggregates, vector search, image transforms, and ranking.
   - device capability probe chooses RAM-only, SSD-backed, NoSQL/vector, or CPU
     storage/offload profile.
4. Production perf evidence:
   - baseline CPU latency/throughput.
   - batch-size sweep, p50/p95/p99 latency, max RSS/VRAM, queue depth, and
     fallback rate.
   - GPU path must win on coarse payload work; small HTTP control-plane work
     stays CPU-only.
