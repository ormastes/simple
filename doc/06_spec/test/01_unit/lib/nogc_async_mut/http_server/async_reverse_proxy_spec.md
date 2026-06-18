# Async Reverse Proxy Policy

> The async worker keeps TCP accept, request parsing, routing, and proxy control decisions on the CPU. These scenarios cover the reusable policy layer that the worker-level streaming proxy state machine will consume.

<!-- sdn-diagram:id=async_reverse_proxy_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=async_reverse_proxy_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

async_reverse_proxy_spec -> std
async_reverse_proxy_spec -> lib
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=async_reverse_proxy_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 101 | 101 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Async Reverse Proxy Policy

The async worker keeps TCP accept, request parsing, routing, and proxy control decisions on the CPU. These scenarios cover the reusable policy layer that the worker-level streaming proxy state machine will consume.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Requirements | doc/02_requirements/feature/gpu_web_db_offload.md |
| Plan | doc/03_plan/agent_tasks/gpu_web_db_offload_impl_status.md |
| Design | doc/05_design/gpu_web_db_offload.md |
| Research | N/A |
| Source | `test/01_unit/lib/nogc_async_mut/http_server/async_reverse_proxy_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

The async worker keeps TCP accept, request parsing, routing, and proxy control
decisions on the CPU. These scenarios cover the reusable policy layer that the
worker-level streaming proxy state machine will consume.

## Requirements

**Requirements:** doc/02_requirements/feature/gpu_web_db_offload.md

- Proxy routes resolve named upstream pools from existing server config.
- Unsafe paths and unsupported methods fail before worker streaming starts.
- Upstream request serialization drops hop-by-hop and authority headers.
- Upstream response headers are filtered before client send.
- Upstream response headers are validated for status syntax, line length, and
  header count before client send.
- Upstream peer health and fail timeout state avoid repeatedly selecting failed
  backends.
- Least-connections selection can use explicit worker-owned peer state.
- Upstream connection pool policy decides when an idle backend fd can be reused
  and when it must be closed or freshly connected.
- `Content-Length` response framing can mark upstream responses complete before
  close-delimited EOF.
- Upstream requests use keep-alive so worker-owned pooled fds can carry later
  proxy requests after a framed response completes.
- Partial upstream request and downstream response writes keep unsent bytes for
  a later send completion instead of treating one write as complete.
- Chunked upstream responses stream decoded complete chunks before client send
  when `Transfer-Encoding` is stripped.
- Oversized fixed client request bodies use worker-level header-first request
  body streaming instead of the fully buffered compatibility path.
- Chunked client request bodies fail closed on the buffered compatibility path
  and use the worker streaming planner for dechunked upstream body writes.

## Plan

**Plan:** doc/03_plan/agent_tasks/gpu_web_db_offload_impl_status.md

## Design

**Design:** doc/05_design/gpu_web_db_offload.md

## Research

**Research:** N/A

## Examples

Use `async_proxy_plan` after route matching. Use
`async_proxy_select_server_with_peers` when a worker has health/connection state
for the upstream pool; otherwise `async_proxy_select_server` preserves the
existing stateless round-robin behavior.

## Scenarios

### async HTTP reverse proxy policy

#### should find tracked worker proxy ops by fd and kind

- Use one shared scan for proxy body send, receive, and retry dispatch guards


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Use one shared scan for proxy body send, receive, and retry dispatch guards")
val fds = [10, 11, 10]
val kinds = [30, 31, 33]
expect(worker_tracked_op_exists(fds, kinds, 10, 30)).to_be(true)
expect(worker_tracked_op_exists(fds, kinds, 10, 33)).to_be(true)
expect(worker_tracked_op_exists(fds, kinds, 11, 30)).to_be(false)
expect(worker_tracked_op_exists([10, 11], [30], 11, 31)).to_be(false)
```

</details>

#### should detect proxy routes from handler type or proxy_pass

- Mark a location as proxy-capable before static file handling


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Mark a location as proxy-capable before static file handling")
val loc = async_proxy_location("backend")
expect(async_proxy_route_enabled(loc)).to_be(true)
```

</details>

#### should resolve configured upstreams with deterministic request index selection

- Choose backend servers from the configured upstream pool
   - Expected: target0.upstream_addr equals `127.0.0.1:3000`
   - Expected: target1.upstream_addr equals `127.0.0.1:3001`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Choose backend servers from the configured upstream pool")
val target0 = async_proxy_resolve_upstream([async_proxy_upstream()], "backend", 0)
val target1 = async_proxy_resolve_upstream([async_proxy_upstream()], "backend", 1)
expect(target0.ok).to_be(true)
expect(target0.upstream_addr).to_equal("127.0.0.1:3000")
expect(target1.ok).to_be(true)
expect(target1.upstream_addr).to_equal("127.0.0.1:3001")
```

</details>

#### should skip unhealthy upstream peers during round robin selection

- Select only peers that are inside their fail budget
- var down = async proxy peer
- down = async proxy peer record failure
   - Expected: target.upstream_addr equals `127.0.0.1:3001`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Select only peers that are inside their fail budget")
var down = async_proxy_peer("127.0.0.1:3000", 1, 1, 1000)
down = async_proxy_peer_record_failure(down, 100)
val up = async_proxy_peer("127.0.0.1:3001", 1, 1, 1000)
val target = async_proxy_select_round_robin_peer([down, up], 0, 200)
expect(async_proxy_peer_healthy(down, 200)).to_be(false)
expect(target.ok).to_be(true)
expect(target.upstream_addr).to_equal("127.0.0.1:3001")
```

</details>

#### should restore failed upstream peers after fail timeout

- Allow a failed backend to re-enter selection after timeout
- var peer = async proxy peer
- peer = async proxy peer record failure


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Allow a failed backend to re-enter selection after timeout")
var peer = async_proxy_peer("127.0.0.1:3000", 1, 1, 1000)
peer = async_proxy_peer_record_failure(peer, 100)
expect(async_proxy_peer_healthy(peer, 999)).to_be(false)
expect(async_proxy_peer_healthy(peer, 1100)).to_be(true)
```

</details>

#### should schedule active health probes by interval

- Decide when a worker should actively probe an upstream peer
   - Expected: first.reason equals `probe-never-run`
   - Expected: early.reason equals `probe-not-due`
   - Expected: due.reason equals `probe-due`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Decide when a worker should actively probe an upstream peer")
val peer = async_proxy_peer("127.0.0.1:3000", 1, 1, 1000)
val first = async_proxy_peer_probe_due(peer, 100, 0, 1000)
val early = async_proxy_peer_probe_due(peer, 500, 100, 1000)
val due = async_proxy_peer_probe_due(peer, 1100, 100, 1000)
expect(first.should_probe).to_be(true)
expect(first.reason).to_equal("probe-never-run")
expect(early.should_probe).to_be(false)
expect(early.reason).to_equal("probe-not-due")
expect(due.should_probe).to_be(true)
expect(due.reason).to_equal("probe-due")
```

</details>

#### should apply active health probe results without changing active requests

- Keep probe accounting separate from client proxy connection counts
- var peer = async proxy peer
- peer = async proxy peer begin
   - Expected: failed.active_connections equals `1`
   - Expected: failed.fail_count equals `1`
   - Expected: failed.last_failure_ms equals `100`
   - Expected: recovered.active_connections equals `1`
   - Expected: recovered.fail_count equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Keep probe accounting separate from client proxy connection counts")
var peer = async_proxy_peer("127.0.0.1:3000", 1, 2, 1000)
peer = async_proxy_peer_begin(peer)
val failed = async_proxy_peer_apply_probe_failure(peer, 100)
val recovered = async_proxy_peer_apply_probe_success(failed)
expect(failed.active_connections).to_equal(1)
expect(failed.fail_count).to_equal(1)
expect(failed.last_failure_ms).to_equal(100)
expect(recovered.active_connections).to_equal(1)
expect(recovered.fail_count).to_equal(0)
```

</details>

#### should plan bounded active health probes from worker peer state

- Select due upstream probes without blocking the event loop on every peer
- async proxy health probe record
- async proxy health probe record
   - Expected: probes.len() equals `1`
   - Expected: probes[0].upstream_addr equals `127.0.0.1:3000`
   - Expected: probes[0].reason equals `probe-due`


<details>
<summary>Executable SSpec</summary>

Runnable source: 18 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Select due upstream probes without blocking the event loop on every peer")
val ready = async_proxy_peer("127.0.0.1:3000", 1, 1, 1000)
val waiting = async_proxy_peer("127.0.0.1:3001", 1, 1, 1000)
val unusable = async_proxy_peer("", 1, 1, 1000)
val records = [
    async_proxy_health_probe_record("127.0.0.1:3000", 100),
    async_proxy_health_probe_record("127.0.0.1:3001", 900)
]
val probes = async_proxy_due_health_probes(
    [ready, waiting, unusable],
    records,
    1200,
    1000,
    1
)
expect(probes.len()).to_equal(1)
expect(probes[0].upstream_addr).to_equal("127.0.0.1:3000")
expect(probes[0].reason).to_equal("probe-due")
```

</details>

#### should record active health probe attempts by upstream address

- Keep per-worker probe timestamps separate from backend health counters
   - Expected: async_proxy_last_probe_ms(updated, "127.0.0.1:3000") equals `500`
   - Expected: async_proxy_last_probe_ms(appended, "127.0.0.1:3000") equals `500`
   - Expected: async_proxy_last_probe_ms(appended, "127.0.0.1:3001") equals `600`
   - Expected: async_proxy_last_probe_ms(appended, "127.0.0.1:3002") equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Keep per-worker probe timestamps separate from backend health counters")
val records = [async_proxy_health_probe_record("127.0.0.1:3000", 100)]
val updated = async_proxy_mark_health_probe_attempt(records, "127.0.0.1:3000", 500)
val appended = async_proxy_mark_health_probe_attempt(updated, "127.0.0.1:3001", 600)
expect(async_proxy_last_probe_ms(updated, "127.0.0.1:3000")).to_equal(500)
expect(async_proxy_last_probe_ms(appended, "127.0.0.1:3000")).to_equal(500)
expect(async_proxy_last_probe_ms(appended, "127.0.0.1:3001")).to_equal(600)
expect(async_proxy_last_probe_ms(appended, "127.0.0.1:3002")).to_equal(0)
```

</details>

#### should export active health probe planner through http server package

- Let server code reuse health probe policy without importing the proxy submodule
   - Expected: probes.len() equals `1`
   - Expected: probes[0].upstream_addr equals `127.0.0.1:3000`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Let server code reuse health probe policy without importing the proxy submodule")
val peer = exported_async_proxy_peer("127.0.0.1:3000", 1, 1, 1000)
val records = [exported_async_proxy_health_probe_record("127.0.0.1:3000", 0)]
val probes = exported_async_proxy_due_health_probes([peer], records, 100, 1000, 1)
expect(probes.len()).to_equal(1)
expect(probes[0].upstream_addr).to_equal("127.0.0.1:3000")
```

</details>

#### should keep configured active health probes disabled by default

- Avoid starting active backend probes unless an upstream enables them
   - Expected: upstream.health_check_interval_ms equals `0`
   - Expected: upstream.health_check_max_probes equals `1`
   - Expected: probes.len() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Avoid starting active backend probes unless an upstream enables them")
val upstream = async_proxy_upstream()
val peers = [async_proxy_peer("127.0.0.1:3000", 1, 1, 1000)]
val probes = async_proxy_due_configured_health_probes(upstream, peers, [], 100)
expect(upstream.health_check_interval_ms).to_equal(0)
expect(upstream.health_check_max_probes).to_equal(1)
expect(probes.len()).to_equal(0)
```

</details>

#### should choose the least loaded healthy upstream for least-connections

- Prefer the lower weighted active connection score
- var busy = async proxy peer
- busy = async proxy peer begin
- busy = async proxy peer begin
   - Expected: async_proxy_peer_score(busy) equals `2000`
   - Expected: async_proxy_peer_score(idle) equals `0`
   - Expected: target.upstream_addr equals `127.0.0.1:3001`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Prefer the lower weighted active connection score")
var busy = async_proxy_peer("127.0.0.1:3000", 1, 1, 1000)
busy = async_proxy_peer_begin(busy)
busy = async_proxy_peer_begin(busy)
val idle = async_proxy_peer("127.0.0.1:3001", 1, 1, 1000)
val target = async_proxy_select_least_connections_peer([busy, idle], 200)
expect(async_proxy_peer_score(busy)).to_equal(2000)
expect(async_proxy_peer_score(idle)).to_equal(0)
expect(target.ok).to_be(true)
expect(target.upstream_addr).to_equal("127.0.0.1:3001")
```

</details>

#### should use upstream least-connections strategy when state is supplied

- Select from explicit peer health state using the configured strategy
- UpstreamServer
- UpstreamServer
- var busy = async proxy peer
- busy = async proxy peer begin
   - Expected: target.upstream_addr equals `127.0.0.1:3001`


<details>
<summary>Executable SSpec</summary>

Runnable source: 17 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Select from explicit peer health state using the configured strategy")
val upstream = UpstreamConfig(
    name: "backend",
    servers: [
        UpstreamServer(addr: "127.0.0.1:3000", weight: 1, max_fails: 1, fail_timeout_ms: 1000),
        UpstreamServer(addr: "127.0.0.1:3001", weight: 1, max_fails: 1, fail_timeout_ms: 1000)
    ],
    strategy: LoadBalanceStrategy.LeastConnections,
    health_check_interval_ms: 0,
    health_check_max_probes: 1
)
var busy = async_proxy_peer("127.0.0.1:3000", 1, 1, 1000)
busy = async_proxy_peer_begin(busy)
val idle = async_proxy_peer("127.0.0.1:3001", 1, 1, 1000)
val target = async_proxy_select_server_with_peers(upstream, [busy, idle], 0, 200)
expect(target.ok).to_be(true)
expect(target.upstream_addr).to_equal("127.0.0.1:3001")
```

</details>

#### should plan proxy routing through worker-owned peer state

- Resolve a route with explicit peer state instead of stateless selection
- UpstreamServer
- UpstreamServer
- var down = async proxy peer
- down = async proxy peer record failure
   - Expected: target.upstream_addr equals `127.0.0.1:3001`


<details>
<summary>Executable SSpec</summary>

Runnable source: 18 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Resolve a route with explicit peer state instead of stateless selection")
val upstream = UpstreamConfig(
    name: "backend",
    servers: [
        UpstreamServer(addr: "127.0.0.1:3000", weight: 1, max_fails: 1, fail_timeout_ms: 1000),
        UpstreamServer(addr: "127.0.0.1:3001", weight: 1, max_fails: 1, fail_timeout_ms: 1000)
    ],
    strategy: LoadBalanceStrategy.RoundRobin,
    health_check_interval_ms: 0,
    health_check_max_probes: 1
)
var down = async_proxy_peer("127.0.0.1:3000", 1, 1, 1000)
down = async_proxy_peer_record_failure(down, 100)
val up = async_proxy_peer("127.0.0.1:3001", 1, 1, 1000)
val req = async_proxy_request("GET", "/api/users", "", [], "")
val target = async_proxy_plan_with_peers(async_proxy_location("backend"), req, [upstream], [down, up], 0, 200)
expect(target.ok).to_be(true)
expect(target.upstream_addr).to_equal("127.0.0.1:3001")
```

</details>

#### should fail closed when worker-owned peer state has no healthy backend

- Return gateway error when every tracked peer is failed
- UpstreamServer
- var down = async proxy peer
- down = async proxy peer record failure
   - Expected: target.status equals `502`
   - Expected: target.reason equals `Upstream has no healthy servers`


<details>
<summary>Executable SSpec</summary>

Runnable source: 17 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Return gateway error when every tracked peer is failed")
val upstream = UpstreamConfig(
    name: "backend",
    servers: [
        UpstreamServer(addr: "127.0.0.1:3000", weight: 1, max_fails: 1, fail_timeout_ms: 1000)
    ],
    strategy: LoadBalanceStrategy.RoundRobin,
    health_check_interval_ms: 0,
    health_check_max_probes: 1
)
var down = async_proxy_peer("127.0.0.1:3000", 1, 1, 1000)
down = async_proxy_peer_record_failure(down, 100)
val req = async_proxy_request("GET", "/api/users", "", [], "")
val target = async_proxy_plan_with_peers(async_proxy_location("backend"), req, [upstream], [down], 0, 200)
expect(target.ok).to_be(false)
expect(target.status).to_equal(502)
expect(target.reason).to_equal("Upstream has no healthy servers")
```

</details>

#### should acquire reusable idle upstream pool entries

- Reuse an idle upstream fd for the same backend address
   - Expected: decision.upstream_fd equals `30`
   - Expected: decision.reason equals `pool-reuse`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Reuse an idle upstream fd for the same backend address")
val config = async_proxy_pool_default_config()
val entry = async_proxy_pool_entry("127.0.0.1:3000", 30, 100)
val decision = async_proxy_pool_acquire([entry], "127.0.0.1:3000", config, 120)
expect(async_proxy_pool_entry_reusable(entry, config, 120)).to_be(true)
expect(decision.ok).to_be(true)
expect(decision.upstream_fd).to_equal(30)
expect(decision.reason).to_equal("pool-reuse")
```

</details>

#### should reject expired or over-reused upstream pool entries

- Force a fresh connect when idle pool entries exceed budgets
- var reused = async proxy pool entry
   - Expected: miss.reason equals `pool-miss`


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Force a fresh connect when idle pool entries exceed budgets")
val config = AsyncProxyPoolConfig(
    max_idle_per_upstream: 2,
    idle_timeout_ms: 100,
    max_reuse_count: 2
)
val expired = async_proxy_pool_entry("127.0.0.1:3000", 30, 100)
var reused = async_proxy_pool_entry("127.0.0.1:3000", 31, 190)
reused.reuse_count = 2
val miss = async_proxy_pool_acquire([expired, reused], "127.0.0.1:3000", config, 250)
expect(async_proxy_pool_entry_reusable(expired, config, 250)).to_be(false)
expect(async_proxy_pool_entry_reusable(reused, config, 250)).to_be(false)
expect(miss.ok).to_be(false)
expect(miss.reason).to_equal("pool-miss")
```

</details>

#### should update upstream pool entries on acquire release and close

- Track active state, reuse count, and closed state
   - Expected: acquired.last_used_ms equals `120`
   - Expected: released.reuse_count equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Track active state, reuse count, and closed state")
val entry = async_proxy_pool_entry("127.0.0.1:3000", 30, 100)
val acquired = async_proxy_pool_mark_acquired(entry, 120)
val released = async_proxy_pool_mark_released(acquired, 150)
val closed = async_proxy_pool_mark_closed(released, 180)
expect(acquired.in_use).to_be(true)
expect(acquired.last_used_ms).to_equal(120)
expect(released.in_use).to_be(false)
expect(released.reuse_count).to_equal(1)
expect(closed.closed).to_be(true)
expect(async_proxy_pool_entry_reusable(closed, async_proxy_pool_default_config(), 181)).to_be(false)
```

</details>

#### should enforce per-upstream idle pool caps

- Limit retained idle connections for a backend
   - Expected: async_proxy_pool_idle_count([first, second], "127.0.0.1:3000", config, 200) equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Limit retained idle connections for a backend")
val config = AsyncProxyPoolConfig(
    max_idle_per_upstream: 1,
    idle_timeout_ms: 1000,
    max_reuse_count: 10
)
val first = async_proxy_pool_entry("127.0.0.1:3000", 30, 100)
val second = async_proxy_pool_entry("127.0.0.1:3001", 31, 100)
expect(async_proxy_pool_idle_count([first, second], "127.0.0.1:3000", config, 200)).to_equal(1)
expect(async_proxy_pool_can_keep_idle([first, second], "127.0.0.1:3000", config, 200)).to_be(false)
expect(async_proxy_pool_can_keep_idle([first, second], "127.0.0.1:3002", config, 200)).to_be(true)
```

</details>

#### should track partial upstream request sends

- Keep request bytes pending until the backend write fully completes
   - Expected: first.request_bytes_sent equals `5`
   - Expected: done.request_bytes_sent equals `conn.request_wire.len()`
   - Expected: async_proxy_request_remaining(done) equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Keep request bytes pending until the backend write fully completes")
val conn = async_proxy_connection(10, "127.0.0.1:3000", "GET / HTTP/1.1\r\nHost: 127.0.0.1:3000\r\n\r\n", 100)
val first = async_proxy_mark_request_sent(conn, 5, 101)
val done = async_proxy_mark_request_sent(first, 1000, 102)
expect(first.request_bytes_sent).to_equal(5)
expect(async_proxy_request_remaining(first)).to_start_with("/ HTTP/1.1")
expect(done.request_bytes_sent).to_equal(conn.request_wire.len())
expect(async_proxy_request_remaining(done)).to_equal("")
```

</details>

#### should keep partial downstream response sends pending

- Trim only the bytes the client write actually accepted
   - Expected: async_proxy_remaining_after_send("abcdef", 2) equals `cdef`
   - Expected: async_proxy_remaining_after_send("abcdef", 99) equals ``
   - Expected: async_proxy_remaining_after_send("abcdef", -1) equals `abcdef`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Trim only the bytes the client write actually accepted")
expect(async_proxy_remaining_after_send("abcdef", 2)).to_equal("cdef")
expect(async_proxy_remaining_after_send("abcdef", 99)).to_equal("")
expect(async_proxy_remaining_after_send("abcdef", -1)).to_equal("abcdef")
```

</details>

#### should apply client backpressure before scheduling another upstream read

- Keep upstream reads paused while unsent client bytes are pending
- var conn = async proxy connection
   - Expected: async_proxy_upstream_recv_budget(conn, 8192) equals `8192`
   - Expected: async_proxy_upstream_recv_budget(conn, 8192) equals `0`
   - Expected: async_proxy_upstream_recv_budget(conn, 8192) equals `4`
   - Expected: async_proxy_upstream_recv_budget(conn, 8192) equals `0`
   - Expected: async_proxy_upstream_recv_budget(conn, 8192) equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 18 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Keep upstream reads paused while unsent client bytes are pending")
var conn = async_proxy_connection(10, "127.0.0.1:3000", "GET / HTTP/1.1\r\n\r\n", 100)
expect(async_proxy_should_recv_upstream(conn)).to_be(true)
expect(async_proxy_upstream_recv_budget(conn, 8192)).to_equal(8192)
conn.pending_client_data = "HTTP/1.1 200 OK\r\n\r\nbody"
expect(async_proxy_should_recv_upstream(conn)).to_be(false)
expect(async_proxy_upstream_recv_budget(conn, 8192)).to_equal(0)
expect(async_proxy_pending_client_over_budget(conn)).to_be(false)
conn.max_pending_client_bytes = 4
expect(async_proxy_pending_client_over_budget(conn)).to_be(true)
conn.pending_client_data = ""
expect(async_proxy_upstream_recv_budget(conn, 8192)).to_equal(4)
conn.pending_client_data = "1234"
expect(async_proxy_upstream_recv_budget(conn, 8192)).to_equal(0)
conn.pending_client_data = ""
conn.response_complete = true
expect(async_proxy_should_recv_upstream(conn)).to_be(false)
expect(async_proxy_upstream_recv_budget(conn, 8192)).to_equal(0)
```

</details>

#### should append response data to pending client buffers before backpressure checks

- Preserve unsent client bytes if policy code prepares another upstream fragment
- var conn = async proxy connection
   - Expected: appended.pending_client_data equals `helloworld`
   - Expected: appended.body_bytes_forwarded equals `5`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Preserve unsent client bytes if policy code prepares another upstream fragment")
var conn = async_proxy_connection(10, "127.0.0.1:3000", "GET / HTTP/1.1\r\n\r\n", 100)
conn.response_headers_done = true
conn.expected_body_bytes = 12
conn.pending_client_data = "hello"
conn.max_pending_client_bytes = 8
val appended = async_proxy_prepare_client_chunk(conn, "world", 101)
expect(appended.pending_client_data).to_equal("helloworld")
expect(appended.body_bytes_forwarded).to_equal(5)
expect(async_proxy_pending_client_over_budget(appended)).to_be(true)
expect(async_proxy_should_recv_upstream(appended)).to_be(false)
```

</details>

#### should stream fixed client request bodies to upstream incrementally

- Send headers once and keep fixed body chunks pending until upstream writes drain
   - Expected: first.pending_upstream_data equals `hello`
   - Expected: done.pending_upstream_data equals `world`
   - Expected: done.bytes_received equals `10`


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Send headers once and keep fixed body chunks pending until upstream writes drain")
val req = async_proxy_request("POST", "/api/upload", "", [("Content-Length", "10"), ("Content-Type", "text/plain")], "")
val stream = async_proxy_request_body_stream_begin(req, "127.0.0.1:3000", 16)
val first = async_proxy_request_stream_receive_fixed(stream, "hello")
val drained = async_proxy_request_stream_mark_upstream_sent(first, 5)
val done = async_proxy_request_stream_receive_fixed(drained, "world")
expect(stream.header_wire).to_contain("Content-Length: 10\r\n")
expect(first.pending_upstream_data).to_equal("hello")
expect(first.complete).to_be(false)
expect(async_proxy_should_recv_client_body(first)).to_be(false)
expect(async_proxy_should_recv_client_body(drained)).to_be(true)
expect(done.pending_upstream_data).to_equal("world")
expect(done.bytes_received).to_equal(10)
expect(done.complete).to_be(true)
```

</details>

#### should dechunk streaming client request bodies before upstream writes

- Decode available request chunks and preserve incomplete chunk bytes
   - Expected: first.pending_upstream_data equals `hello`
   - Expected: done.pending_upstream_data equals ``
   - Expected: done.bytes_received equals `5`


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Decode available request chunks and preserve incomplete chunk bytes")
val req = async_proxy_request("POST", "/api/upload", "", [("Transfer-Encoding", "chunked")], "")
val stream = async_proxy_request_body_stream_begin(req, "127.0.0.1:3000", 16)
val first = async_proxy_request_stream_receive_chunked(stream, "5\r\nhello\r\n")
val drained = async_proxy_request_stream_mark_upstream_sent(first, 5)
val done = async_proxy_request_stream_receive_chunked(drained, "0\r\n\r\n")
expect(stream.header_wire).to_contain("Transfer-Encoding: chunked\r\n")
expect(first.pending_upstream_data).to_equal("hello")
expect(first.complete).to_be(false)
expect(done.pending_upstream_data).to_equal("")
expect(done.bytes_received).to_equal(5)
expect(done.complete).to_be(true)
expect(done.valid).to_be(true)
```

</details>

#### should preserve chunk framing for early chunked proxy handoff

- Forward complete raw chunk frames while counting decoded payload bytes
   - Expected: first.pending_upstream_data equals ``
   - Expected: first.chunked_body_buffer equals `5\r\nhe`
   - Expected: second.pending_upstream_data equals `5\r\nhello\r\n`
   - Expected: done.pending_upstream_data equals `5\r\nhello\r\n0\r\n\r\n`
   - Expected: done.bytes_received equals `5`


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Forward complete raw chunk frames while counting decoded payload bytes")
val req = async_proxy_request("POST", "/api/upload", "", [("Transfer-Encoding", "chunked")], "")
val stream = async_proxy_request_body_stream_begin(req, "127.0.0.1:3000", 16)
val first = async_proxy_request_stream_receive_chunked_framed(stream, "5\r\nhe")
val second = async_proxy_request_stream_receive_chunked_framed(first, "llo\r\n0\r\n")
val done = async_proxy_request_stream_receive_chunked_framed(second, "\r\n")
expect(stream.header_wire).to_contain("Transfer-Encoding: chunked\r\n")
expect(first.pending_upstream_data).to_equal("")
expect(first.chunked_body_buffer).to_equal("5\r\nhe")
expect(second.pending_upstream_data).to_equal("5\r\nhello\r\n")
expect(second.complete).to_be(false)
expect(done.pending_upstream_data).to_equal("5\r\nhello\r\n0\r\n\r\n")
expect(done.bytes_received).to_equal(5)
expect(done.complete).to_be(true)
expect(done.valid).to_be(true)
```

</details>

#### should reject malformed and trailing chunked proxy handoff bytes

- Fail closed on bad chunk framing or bytes after the terminal chunk
   - Expected: bad_hex.error equals `chunked-request-body-malformed`
   - Expected: missing_crlf.error equals `chunked-request-body-malformed`
   - Expected: trailing.error equals `chunked-request-body-trailing-bytes`


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Fail closed on bad chunk framing or bytes after the terminal chunk")
val req = async_proxy_request("POST", "/api/upload", "", [("Transfer-Encoding", "chunked")], "")
val stream = async_proxy_request_body_stream_begin(req, "127.0.0.1:3000", 16)
val bad_hex = async_proxy_request_stream_receive_chunked_framed(stream, "z\r\nbad\r\n")
val missing_crlf = async_proxy_request_stream_receive_chunked_framed(stream, "5\r\nhelloX")
val trailing = async_proxy_request_stream_receive_chunked_framed(stream, "0\r\n\r\nGET /next HTTP/1.1\r\n\r\n")
expect(bad_hex.valid).to_be(false)
expect(bad_hex.error).to_equal("chunked-request-body-malformed")
expect(missing_crlf.valid).to_be(false)
expect(missing_crlf.error).to_equal("chunked-request-body-malformed")
expect(trailing.valid).to_be(false)
expect(trailing.error).to_equal("chunked-request-body-trailing-bytes")
```

</details>

#### should budget incomplete chunked proxy handoff staging bytes

- Bound the chunked decode staging buffer, not only pending upstream bytes
   - Expected: partial.pending_upstream_data equals ``
   - Expected: partial.chunked_body_buffer equals `5\r\nhe`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Bound the chunked decode staging buffer, not only pending upstream bytes")
val req = async_proxy_request("POST", "/api/upload", "", [("Transfer-Encoding", "chunked")], "")
val stream = async_proxy_request_body_stream_begin(req, "127.0.0.1:3000", 4)
val partial = async_proxy_request_stream_receive_chunked_framed(stream, "5\r\nhe")
expect(partial.pending_upstream_data).to_equal("")
expect(partial.chunked_body_buffer).to_equal("5\r\nhe")
expect(async_proxy_request_pending_over_budget(partial)).to_be(true)
```

</details>

#### should apply upstream backpressure before reading more client request body

- Pause client-body reads while upstream body bytes are pending or over budget
   - Expected: first.pending_upstream_data equals `abcde`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Pause client-body reads while upstream body bytes are pending or over budget")
val req = async_proxy_request("POST", "/api/upload", "", [("Content-Length", "8")], "")
val stream = async_proxy_request_body_stream_begin(req, "127.0.0.1:3000", 4)
val first = async_proxy_request_stream_receive_fixed(stream, "abcde")
expect(first.pending_upstream_data).to_equal("abcde")
expect(async_proxy_should_recv_client_body(first)).to_be(false)
expect(async_proxy_request_pending_over_budget(first)).to_be(true)
val drained = async_proxy_request_stream_mark_upstream_sent(first, 5)
expect(async_proxy_should_recv_client_body(drained)).to_be(true)
expect(async_proxy_request_pending_over_budget(drained)).to_be(false)
```

</details>

#### should parse fixed streaming proxy requests at header completion

- Expose the initial body fragment before the normal parser buffers the full upload
   - Expected: parsed.request.method equals `POST`
   - Expected: parsed.request.path equals `/api/upload`
   - Expected: parsed.request.query equals `tenant=a`
   - Expected: parsed.request.body equals `hello`
   - Expected: parsed.body_fragment equals `hello`


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Expose the initial body fragment before the normal parser buffers the full upload")
val parsed = async_proxy_parse_header_request(
    "POST /api/upload?tenant=a HTTP/1.1\r\nHost: public.example\r\nContent-Length: 1048577\r\nContent-Type: text/plain\r\n\r\nhello",
    "127.0.0.1:10000"
)
expect(parsed.ok).to_be(true)
expect(parsed.request.method).to_equal("POST")
expect(parsed.request.path).to_equal("/api/upload")
expect(parsed.request.query).to_equal("tenant=a")
expect(parsed.request.body).to_equal("hello")
expect(parsed.body_fragment).to_equal("hello")
expect(async_proxy_request_body_streaming_required(parsed.request, 1024 * 1024)).to_be(true)
expect(async_proxy_request_transfer_chunked(parsed.request)).to_be(false)
```

</details>

#### should leave incomplete proxy headers on the normal parser path

- Avoid claiming a streaming request before the header delimiter arrives
   - Expected: parsed.reason equals `headers-incomplete`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Avoid claiming a streaming request before the header delimiter arrives")
val parsed = async_proxy_parse_header_request(
    "POST /api/upload HTTP/1.1\r\nHost: public.example\r\nContent-Length: 1048577\r\n",
    "127.0.0.1:10000"
)
expect(parsed.ok).to_be(false)
expect(parsed.reason).to_equal("headers-incomplete")
```

</details>

#### should parse chunked streaming proxy requests at header completion

- Start chunked proxy upload streaming without waiting for the terminal chunk
   - Expected: body.pending_upstream_data equals ``
   - Expected: body.chunked_body_buffer equals `5\r\nhe`


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Start chunked proxy upload streaming without waiting for the terminal chunk")
val parsed = async_proxy_parse_header_request(
    "POST /api/upload HTTP/1.1\r\nHost: public.example\r\nTransfer-Encoding: chunked\r\n\r\n5\r\nhe",
    "127.0.0.1:10000"
)
val stream = async_proxy_request_body_stream_begin(parsed.request, "127.0.0.1:3000", 16)
val body = async_proxy_request_stream_receive_chunked_framed(stream, parsed.body_fragment)
expect(parsed.ok).to_be(true)
expect(async_proxy_request_transfer_chunked(parsed.request)).to_be(true)
expect(body.pending_upstream_data).to_equal("")
expect(body.chunked_body_buffer).to_equal("5\r\nhe")
expect(body.complete).to_be(false)
```

</details>

#### should preserve initial live chunked upload fragments before later body reads

- Apply the framed chunk parser to the first body bytes captured with headers
   - Expected: initial.pending_upstream_data equals ``
   - Expected: initial.chunked_body_buffer equals `5\r\nh`
   - Expected: next.pending_upstream_data equals `5\r\nhello\r\n`
   - Expected: next.chunked_body_buffer equals `6\r`
   - Expected: next.bytes_received equals `5`


<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Apply the framed chunk parser to the first body bytes captured with headers")
val parsed = async_proxy_parse_header_request(
    "POST /api/upload-chunked HTTP/1.1\r\nHost: public.example\r\nTransfer-Encoding: chunked\r\nConnection: close\r\n\r\n5\r\nh",
    "127.0.0.1:10000"
)
val stream = async_proxy_request_body_stream_begin(parsed.request, "127.0.0.1:3000", 1024)
val initial = async_proxy_request_stream_receive_chunked_framed(stream, parsed.body_fragment)
val next = async_proxy_request_stream_receive_chunked_framed(initial, "ello\r\n6\r")
expect(parsed.ok).to_be(true)
expect(initial.valid).to_be(true)
expect(initial.pending_upstream_data).to_equal("")
expect(initial.chunked_body_buffer).to_equal("5\r\nh")
expect(next.valid).to_be(true)
expect(next.pending_upstream_data).to_equal("5\r\nhello\r\n")
expect(next.chunked_body_buffer).to_equal("6\r")
expect(next.bytes_received).to_equal(5)
```

</details>

#### should pass through live chunked request bytes without proxy-side dechunking

- Preserve raw chunk framing for the worker hot path
   - Expected: initial.pending_upstream_data equals `5\r\nh`
   - Expected: done.pending_upstream_data equals `ello\r\n0\r\n\r\n`


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Preserve raw chunk framing for the worker hot path")
val req = async_proxy_request("POST", "/api/upload", "", [("Transfer-Encoding", "chunked")], "")
val stream = async_proxy_request_body_stream_begin(req, "127.0.0.1:3000", 1024)
val initial = async_proxy_request_stream_receive_chunked_passthrough(stream, "5\r\nh")
val middle = async_proxy_request_stream_mark_upstream_sent(initial, initial.pending_upstream_data.len())
val done = async_proxy_request_stream_receive_chunked_passthrough(middle, "ello\r\n0\r\n\r\n")
expect(initial.valid).to_be(true)
expect(initial.pending_upstream_data).to_equal("5\r\nh")
expect(initial.complete).to_be(false)
expect(done.valid).to_be(true)
expect(done.pending_upstream_data).to_equal("ello\r\n0\r\n\r\n")
expect(done.complete).to_be(true)
```

</details>

#### should not treat terminal-looking bytes inside chunk data as upload completion

- Use structural chunk parsing for pass-through completion detection
   - Expected: body.pending_upstream_data equals `5\r\n\r\n0\r\n\r\n`
   - Expected: body.chunked_body_buffer equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Use structural chunk parsing for pass-through completion detection")
val req = async_proxy_request("POST", "/api/upload", "", [("Transfer-Encoding", "chunked")], "")
val stream = async_proxy_request_body_stream_begin(req, "127.0.0.1:3000", 1024)
val body = async_proxy_request_stream_receive_chunked_passthrough(stream, "5\r\n\r\n0\r\n\r\n")
expect(body.valid).to_be(true)
expect(body.pending_upstream_data).to_equal("5\r\n\r\n0\r\n\r\n")
expect(body.complete).to_be(false)
expect(body.chunked_body_buffer).to_equal("")
```

</details>

#### should reject trailing bytes after pass-through chunked upload completion

- Fail closed instead of forwarding request smuggling bytes after the terminal chunk
   - Expected: trailing.error equals `chunked-request-body-trailing-bytes`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Fail closed instead of forwarding request smuggling bytes after the terminal chunk")
val req = async_proxy_request("POST", "/api/upload", "", [("Transfer-Encoding", "chunked")], "")
val stream = async_proxy_request_body_stream_begin(req, "127.0.0.1:3000", 1024)
val trailing = async_proxy_request_stream_receive_chunked_passthrough(stream, "0\r\n\r\nGET /next HTTP/1.1\r\n\r\n")
expect(trailing.valid).to_be(false)
expect(trailing.complete).to_be(false)
expect(trailing.error).to_equal("chunked-request-body-trailing-bytes")
```

</details>

#### should fail closed when upstream config is missing

- Return a gateway error instead of falling through to static serving
   - Expected: plan.status equals `502`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Return a gateway error instead of falling through to static serving")
val req = async_proxy_request("GET", "/api/users", "", [], "")
val plan = async_proxy_plan(async_proxy_location("missing"), req, [async_proxy_upstream()], 0)
expect(plan.ok).to_be(false)
expect(plan.status).to_equal(502)
```

</details>

#### should reject unsafe proxy paths before worker streaming

- Reject traversal before opening an upstream connection
   - Expected: plan.status equals `400`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Reject traversal before opening an upstream connection")
val req = async_proxy_request("GET", "/api/../secret", "", [], "")
val plan = async_proxy_plan(async_proxy_location("backend"), req, [async_proxy_upstream()], 0)
expect(plan.ok).to_be(false)
expect(plan.status).to_equal(400)
```

</details>

#### should reject CONNECT and other control-plane methods

- Keep HTTP tunnel setup out of the normal proxy path
   - Expected: plan.status equals `405`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Keep HTTP tunnel setup out of the normal proxy path")
val req = async_proxy_request("CONNECT", "/api/tunnel", "", [], "")
val plan = async_proxy_plan(async_proxy_location("backend"), req, [async_proxy_upstream()], 0)
expect(plan.ok).to_be(false)
expect(plan.status).to_equal(405)
```

</details>

#### should reject chunked proxy request bodies until streaming is implemented

- Avoid dropping a request body by stripping Transfer-Encoding
   - Expected: plan.status equals `501`
   - Expected: plan.reason equals `Proxy chunked request body streaming unsupported`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Avoid dropping a request body by stripping Transfer-Encoding")
val req = async_proxy_request("POST", "/api/upload", "", [("Transfer-Encoding", "chunked")], "5\r\nhello\r\n0\r\n\r\n")
val plan = async_proxy_plan(async_proxy_location("backend"), req, [async_proxy_upstream()], 0)
expect(async_proxy_request_transfer_chunked(req)).to_be(true)
expect(plan.ok).to_be(false)
expect(plan.status).to_equal(501)
expect(plan.reason).to_equal("Proxy chunked request body streaming unsupported")
```

</details>

#### should detect request chunked transfer tokens without substring matches

- Treat Transfer-Encoding chunked as a comma token, not a substring


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Treat Transfer-Encoding chunked as a comma token, not a substring")
val comma_token = async_proxy_request("POST", "/api/upload", "", [("Transfer-Encoding", "ChUnKeD")], "")
val mixed = async_proxy_request("POST", "/api/upload", "", [("Transfer-Encoding", "gzip, ChUnKeD")], "")
val substring = async_proxy_request("POST", "/api/upload", "", [("Transfer-Encoding", "xchunked")], "")
expect(async_proxy_request_transfer_chunked(comma_token)).to_be(true)
expect(async_proxy_request_transfer_chunked(mixed)).to_be(true)
expect(async_proxy_request_unsupported_transfer_encoding(mixed)).to_be(true)
expect(async_proxy_request_transfer_chunked(substring)).to_be(false)
```

</details>

#### should reject conflicting proxy request body framing

- Fail closed before forwarding Content-Length plus Transfer-Encoding
- async proxy location
- [async proxy upstream
- [async proxy peer
   - Expected: buffered.status equals `400`
   - Expected: buffered.reason equals `Proxy request framing conflict`
   - Expected: streaming.status equals `400`
   - Expected: streaming.reason equals `Proxy request framing conflict`


<details>
<summary>Executable SSpec</summary>

Runnable source: 18 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Fail closed before forwarding Content-Length plus Transfer-Encoding")
val req = async_proxy_request("POST", "/api/upload", "", [("Content-Length", "5"), ("Transfer-Encoding", "chunked")], "5\r\nhello\r\n0\r\n\r\n")
val buffered = async_proxy_plan(async_proxy_location("backend"), req, [async_proxy_upstream()], 0)
val streaming = async_proxy_plan_with_peers_for_request_stream(
    async_proxy_location("backend"),
    req,
    [async_proxy_upstream()],
    [async_proxy_peer("127.0.0.1:3000", 1, 1, 1000)],
    0,
    200
)
expect(async_proxy_request_framing_conflict(req)).to_be(true)
expect(buffered.ok).to_be(false)
expect(buffered.status).to_equal(400)
expect(buffered.reason).to_equal("Proxy request framing conflict")
expect(streaming.ok).to_be(false)
expect(streaming.status).to_equal(400)
expect(streaming.reason).to_equal("Proxy request framing conflict")
```

</details>

#### should reject invalid or conflicting proxy request content lengths

- Fail closed before forwarding ambiguous request body length
   - Expected: invalid_plan.status equals `400`
   - Expected: invalid_plan.reason equals `Proxy request content length invalid`
   - Expected: mismatch_plan.status equals `400`
   - Expected: mismatch_plan.reason equals `Proxy request content length conflict`


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Fail closed before forwarding ambiguous request body length")
val invalid = async_proxy_request("POST", "/api/upload", "", [("Content-Length", "nope")], "hello")
val mismatch = async_proxy_request("POST", "/api/upload", "", [("Content-Length", "5"), ("Content-Length", "7")], "hello")
val duplicate = async_proxy_request("POST", "/api/upload", "", [("Content-Length", "5"), ("Content-Length", "5")], "hello")
val invalid_plan = async_proxy_plan(async_proxy_location("backend"), invalid, [async_proxy_upstream()], 0)
val mismatch_plan = async_proxy_plan(async_proxy_location("backend"), mismatch, [async_proxy_upstream()], 0)
val duplicate_plan = async_proxy_plan(async_proxy_location("backend"), duplicate, [async_proxy_upstream()], 0)
expect(async_proxy_request_content_length_invalid(invalid)).to_be(true)
expect(async_proxy_request_content_length_conflict(mismatch)).to_be(true)
expect(async_proxy_request_content_length_conflict(duplicate)).to_be(false)
expect(invalid_plan.status).to_equal(400)
expect(invalid_plan.reason).to_equal("Proxy request content length invalid")
expect(mismatch_plan.status).to_equal(400)
expect(mismatch_plan.reason).to_equal("Proxy request content length conflict")
expect(duplicate_plan.ok).to_be(true)
```

</details>

#### should reject unsupported proxy request transfer encodings

- Do not strip an unknown Transfer-Encoding and forward changed body semantics
   - Expected: plan.status equals `501`
   - Expected: plan.reason equals `Proxy transfer encoding unsupported`
   - Expected: mixed_plan.status equals `501`
   - Expected: mixed_plan.reason equals `Proxy transfer encoding unsupported`


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Do not strip an unknown Transfer-Encoding and forward changed body semantics")
val req = async_proxy_request("POST", "/api/upload", "", [("Transfer-Encoding", "gzip")], "compressed")
val mixed = async_proxy_request("POST", "/api/upload", "", [("Transfer-Encoding", "gzip, chunked")], "compressed")
val plan = async_proxy_plan(async_proxy_location("backend"), req, [async_proxy_upstream()], 0)
val mixed_plan = async_proxy_plan(async_proxy_location("backend"), mixed, [async_proxy_upstream()], 0)
expect(async_proxy_request_has_transfer_encoding(req)).to_be(true)
expect(async_proxy_request_transfer_chunked(req)).to_be(false)
expect(async_proxy_request_unsupported_transfer_encoding(req)).to_be(true)
expect(plan.ok).to_be(false)
expect(plan.status).to_equal(501)
expect(plan.reason).to_equal("Proxy transfer encoding unsupported")
expect(async_proxy_request_transfer_chunked(mixed)).to_be(true)
expect(async_proxy_request_unsupported_transfer_encoding(mixed)).to_be(true)
expect(mixed_plan.status).to_equal(501)
expect(mixed_plan.reason).to_equal("Proxy transfer encoding unsupported")
```

</details>

#### should resolve chunked bodies for worker dechunked request streaming

- Keep buffered compatibility fail-closed while allowing Worker to dechunk body writes
- async proxy location
- [async proxy upstream
- [async proxy peer
   - Expected: body.pending_upstream_data equals `hello`


<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Keep buffered compatibility fail-closed while allowing Worker to dechunk body writes")
val req = async_proxy_request("POST", "/api/upload", "", [("Transfer-Encoding", "chunked")], "5\r\nhello\r\n0\r\n\r\n")
val plan = async_proxy_plan_with_peers_for_request_stream(
    async_proxy_location("backend"),
    req,
    [async_proxy_upstream()],
    [async_proxy_peer("127.0.0.1:3000", 1, 1, 1000)],
    0,
    200
)
val stream = async_proxy_dechunked_request_body_stream_begin(req, "127.0.0.1:3000", 5, 16)
val body = async_proxy_request_stream_receive_chunked(stream, req.body)
expect(plan.ok).to_be(true)
expect(stream.header_wire).to_contain("Content-Length: 5\r\n")
expect(body.pending_upstream_data).to_equal("hello")
expect(body.complete).to_be(true)
```

</details>

#### should allow bounded fixed request bodies without streaming

- Keep small parsed request bodies on the buffered compatibility path
- async proxy location
- [async proxy upstream


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Keep small parsed request bodies on the buffered compatibility path")
val req = async_proxy_request("POST", "/api/upload", "", [("Content-Type", "text/plain")], "small-body")
val plan = async_proxy_plan_with_request_limit(
    async_proxy_location("backend"),
    req,
    [async_proxy_upstream()],
    0,
    16
)
expect(async_proxy_request_body_streaming_required(req, 16)).to_be(false)
expect(plan.ok).to_be(true)
```

</details>

#### should reject oversized fixed request bodies before upstream selection

- Fail closed instead of silently full-buffering a large proxy body
- async proxy location
- [async proxy upstream
   - Expected: plan.status equals `413`
   - Expected: plan.reason equals `Proxy request body streaming required`


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Fail closed instead of silently full-buffering a large proxy body")
val req = async_proxy_request("POST", "/api/upload", "", [("Content-Type", "text/plain")], "large")
val plan = async_proxy_plan_with_request_limit(
    async_proxy_location("backend"),
    req,
    [async_proxy_upstream()],
    0,
    4
)
expect(async_proxy_request_body_streaming_required(req, 4)).to_be(true)
expect(plan.ok).to_be(false)
expect(plan.status).to_equal(413)
expect(plan.reason).to_equal("Proxy request body streaming required")
```

</details>

#### should reject oversized fixed request bodies before peer-aware selection

- Keep health/load-balancing state untouched for streaming-required bodies
- async proxy location
- [async proxy upstream
- [async proxy peer
   - Expected: plan.status equals `413`
   - Expected: plan.reason equals `Proxy request body streaming required`


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Keep health/load-balancing state untouched for streaming-required bodies")
val req = async_proxy_request("POST", "/api/upload", "", [("Content-Type", "text/plain")], "large")
val plan = async_proxy_plan_with_peers_and_request_limit(
    async_proxy_location("backend"),
    req,
    [async_proxy_upstream()],
    [async_proxy_peer("127.0.0.1:3000", 1, 1, 1000)],
    0,
    100,
    4
)
expect(plan.ok).to_be(false)
expect(plan.status).to_equal(413)
expect(plan.reason).to_equal("Proxy request body streaming required")
```

</details>

#### should resolve oversized fixed bodies for worker request streaming

- Let the worker select a healthy upstream before scheduling header and body sends separately
- async proxy location
- [async proxy upstream
   - Expected: plan.upstream_addr equals `127.0.0.1:3001`


<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Let the worker select a healthy upstream before scheduling header and body sends separately")
val req = async_proxy_request("POST", "/api/upload", "", [("Content-Type", "text/plain")], "large")
val down = async_proxy_peer("127.0.0.1:3000", 1, 1, 1000)
val up = async_proxy_peer("127.0.0.1:3001", 1, 1, 1000)
val failed = async_proxy_peer_apply_probe_failure(down, 100)
val plan = async_proxy_plan_with_peers_for_request_stream(
    async_proxy_location("backend"),
    req,
    [async_proxy_upstream()],
    [failed, up],
    0,
    200
)
expect(async_proxy_request_body_streaming_required(req, 4)).to_be(true)
expect(plan.ok).to_be(true)
expect(plan.upstream_addr).to_equal("127.0.0.1:3001")
```

</details>

#### should reject upgrade requests until tunneling is implemented

- Do not downgrade WebSocket upgrade requests into normal GET proxying
   - Expected: plan.status equals `501`
   - Expected: plan.reason equals `Proxy upgrade tunneling unsupported`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Do not downgrade WebSocket upgrade requests into normal GET proxying")
val req = async_proxy_request("GET", "/ws", "", [("Connection", "Upgrade"), ("Upgrade", "websocket")], "")
val plan = async_proxy_plan(async_proxy_location("backend"), req, [async_proxy_upstream()], 0)
expect(async_proxy_request_upgrade(req)).to_be(true)
expect(plan.ok).to_be(false)
expect(plan.status).to_equal(501)
expect(plan.reason).to_equal("Proxy upgrade tunneling unsupported")
```

</details>

#### should reject upgrade requests before peer-aware upstream selection

- Keep health/load-balancing state untouched for unsupported upgrade traffic
- async proxy location
- [async proxy upstream
- [async proxy peer
   - Expected: plan.status equals `501`
   - Expected: plan.reason equals `Proxy upgrade tunneling unsupported`


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Keep health/load-balancing state untouched for unsupported upgrade traffic")
val req = async_proxy_request("GET", "/ws", "", [("Connection", "keep-alive, Upgrade"), ("Upgrade", "websocket")], "")
val plan = async_proxy_plan_with_peers(
    async_proxy_location("backend"),
    req,
    [async_proxy_upstream()],
    [async_proxy_peer("127.0.0.1:3000", 1, 1, 1000)],
    0,
    100
)
expect(async_proxy_request_upgrade(req)).to_be(true)
expect(plan.ok).to_be(false)
expect(plan.status).to_equal(501)
expect(plan.reason).to_equal("Proxy upgrade tunneling unsupported")
```

</details>

#### should detect request upgrade connection tokens without substring matches

- Treat Connection upgrade as a comma token, not a substring


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Treat Connection upgrade as a comma token, not a substring")
val comma_token = async_proxy_request("GET", "/ws", "", [("Connection", "keep-alive, UpGrAdE")], "")
val substring = async_proxy_request("GET", "/plain", "", [("Connection", "xupgrade")], "")
expect(async_proxy_header_value_has_token("keep-alive, UpGrAdE", "upgrade")).to_be(true)
expect(async_proxy_header_value_has_token("xupgrade", "upgrade")).to_be(false)
expect(async_proxy_request_upgrade(comma_token)).to_be(true)
expect(async_proxy_request_upgrade(substring)).to_be(false)
```

</details>

#### should plan upgrade tunnels separately from normal proxying

- Resolve the upstream for a future worker tunnel state machine
   - Expected: async_proxy_tunnel_kind(req) equals `upgrade`
   - Expected: plan.upstream_addr equals `127.0.0.1:3000`
   - Expected: plan.tunnel_kind equals `upgrade`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Resolve the upstream for a future worker tunnel state machine")
val req = async_proxy_request("GET", "/ws", "", [("Connection", "keep-alive, Upgrade"), ("Upgrade", "websocket")], "")
val plan = async_proxy_tunnel_plan(async_proxy_location("backend"), req, [async_proxy_upstream()], 0)
expect(async_proxy_tunnel_requested(req)).to_be(true)
expect(async_proxy_tunnel_kind(req)).to_equal("upgrade")
expect(plan.ok).to_be(true)
expect(plan.upstream_addr).to_equal("127.0.0.1:3000")
expect(plan.tunnel_kind).to_equal("upgrade")
```

</details>

#### should preserve upgrade headers in tunnel request serialization

- Serialize WebSocket setup without normal hop-by-hop stripping
-
-
-
-
-
-
-


<details>
<summary>Executable SSpec</summary>

Runnable source: 26 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Serialize WebSocket setup without normal hop-by-hop stripping")
val req = async_proxy_request(
    "GET",
    "/ws",
    "",
    [
        ("Host", "public.example"),
        ("Connection", "keep-alive, Upgrade"),
        ("Keep-Alive", "timeout=5"),
        ("TE", "trailers"),
        ("Trailer", "Digest"),
        ("Upgrade", "websocket"),
        ("Sec-WebSocket-Key", "abc")
    ],
    ""
)
val wire = async_proxy_serialize_tunnel_request(req, "127.0.0.1:3000")
expect(wire).to_start_with("GET /ws HTTP/1.1\r\n")
expect(wire).to_contain("Host: 127.0.0.1:3000\r\n")
expect(wire).to_contain("Connection: Upgrade\r\n")
expect(wire).to_contain("Upgrade: websocket\r\n")
expect(wire).to_contain("Sec-WebSocket-Key: abc\r\n")
expect(wire.contains("Keep-Alive:")).to_be(false)
expect(wire.contains("TE:")).to_be(false)
expect(wire.contains("Trailer:")).to_be(false)
expect(wire).to_end_with("\r\n\r\n")
```

</details>

#### should plan CONNECT tunnels through peer-aware upstream selection

- Keep CONNECT setup separate from normal proxy method admission
- async proxy location
- [async proxy upstream
- [async proxy peer
   - Expected: async_proxy_tunnel_kind(req) equals `connect`
   - Expected: plan.upstream_addr equals `127.0.0.1:3001`
   - Expected: plan.tunnel_kind equals `connect`


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Keep CONNECT setup separate from normal proxy method admission")
val req = async_proxy_request("CONNECT", "/tunnel", "", [], "")
val plan = async_proxy_tunnel_plan_with_peers(
    async_proxy_location("backend"),
    req,
    [async_proxy_upstream()],
    [async_proxy_peer("127.0.0.1:3001", 1, 1, 1000)],
    0,
    100
)
expect(async_proxy_tunnel_kind(req)).to_equal("connect")
expect(plan.ok).to_be(true)
expect(plan.upstream_addr).to_equal("127.0.0.1:3001")
expect(plan.tunnel_kind).to_equal("connect")
```

</details>

#### should serialize upstream requests with hop-by-hop headers removed

- Rewrite host, upstream keep-alive semantics, forwarded address, and content length
- [


<details>
<summary>Executable SSpec</summary>

Runnable source: 19 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Rewrite host, upstream keep-alive semantics, forwarded address, and content length")
val req = async_proxy_request(
    "POST",
    "/api/users",
    "page=1",
    [("Host", "public.example"), ("Connection", "keep-alive"), ("Content-Length", "999"), ("Content-Type", "application/json")],
    "{\"name\":\"Ada\"}"
)
val wire = async_proxy_serialize_request(req, "127.0.0.1:3000")
expect(wire).to_start_with("POST /api/users?page=1 HTTP/1.1\r\n")
expect(wire).to_contain("Host: 127.0.0.1:3000\r\n")
expect(wire).to_contain("Connection: keep-alive\r\n")
expect(wire).to_contain("Content-Length: 14\r\n")
expect(wire).to_contain("X-Forwarded-For: 10.0.0.8\r\n")
expect(wire).to_contain("Content-Type: application/json\r\n")
expect(wire).to_end_with("\r\n\r\n{\"name\":\"Ada\"}")
expect(wire.contains("public.example")).to_be(false)
expect(wire.contains("keep-alive")).to_be(false)
expect(wire.contains("999")).to_be(false)
```

</details>

#### should filter upstream response hop-by-hop headers before client send

- Preserve end-to-end response headers and force close-delimited client output


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Preserve end-to-end response headers and force close-delimited client output")
val filtered = exported_async_proxy_filter_response_headers(
    "HTTP/1.1 200 OK\r\nConnection: keep-alive\r\nTransfer-Encoding: chunked\r\nContent-Type: application/json"
)
expect(filtered).to_start_with("HTTP/1.1 200 OK\r\n")
expect(filtered).to_contain("Content-Type: application/json\r\n")
expect(filtered).to_contain("Connection: close\r\n\r\n")
expect(filtered.contains("keep-alive")).to_be(false)
expect(filtered.contains("Transfer-Encoding")).to_be(false)
```

</details>

#### should dechunk upstream responses before client send

- Strip chunk framing when Transfer-Encoding is removed
   - Expected: async_proxy_dechunk_body("5\r\nhello\r\n0\r\n\r\n").unwrap() equals `hello`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Strip chunk framing when Transfer-Encoding is removed")
val conn = async_proxy_connection(10, "127.0.0.1:3000", "GET / HTTP/1.1\r\n\r\n", 100)
val complete = async_proxy_prepare_client_chunk(conn, "HTTP/1.1 200 OK\r\nTransfer-Encoding: chunked\r\nContent-Type: text/plain\r\n\r\n5\r\nhello\r\n0\r\n\r\n", 101)
expect(async_proxy_transfer_chunked("HTTP/1.1 200 OK\r\nTransfer-Encoding: chunked")).to_be(true)
expect(async_proxy_chunked_body_complete("5\r\nhello\r\n0\r\n\r\n")).to_be(true)
expect(async_proxy_dechunk_body("5\r\nhello\r\n0\r\n\r\n").unwrap()).to_equal("hello")
expect(complete.response_chunked).to_be(true)
expect(async_proxy_response_complete(complete)).to_be(true)
expect(complete.pending_client_data).to_contain("Content-Type: text/plain\r\n")
expect(complete.pending_client_data.contains("Transfer-Encoding")).to_be(false)
expect(complete.pending_client_data).to_end_with("\r\n\r\nhello")
```

</details>

#### should detect response chunked transfer tokens without substring matches

- Only a real Transfer-Encoding chunked token enables response dechunking


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Only a real Transfer-Encoding chunked token enables response dechunking")
expect(async_proxy_transfer_chunked("HTTP/1.1 200 OK\r\nTransfer-Encoding: gzip, ChUnKeD")).to_be(true)
expect(async_proxy_response_unsupported_transfer_encoding("HTTP/1.1 200 OK\r\nTransfer-Encoding: gzip, ChUnKeD")).to_be(true)
expect(async_proxy_transfer_chunked("HTTP/1.1 200 OK\r\nTransfer-Encoding: xchunked")).to_be(false)
```

</details>

#### should stream complete chunked upstream body pieces before terminating chunk

- Send decoded complete chunks while retaining only an incomplete chunk fragment
   - Expected: first.chunked_body_buffer equals `3\r\nl`
   - Expected: first.body_bytes_forwarded equals `2`
   - Expected: second.pending_client_data equals `llo`
   - Expected: second.body_bytes_forwarded equals `5`


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Send decoded complete chunks while retaining only an incomplete chunk fragment")
val conn = async_proxy_connection(10, "127.0.0.1:3000", "GET / HTTP/1.1\r\n\r\n", 100)
val first = async_proxy_prepare_client_chunk(conn, "HTTP/1.1 200 OK\r\nTransfer-Encoding: chunked\r\nContent-Type: text/plain\r\n\r\n2\r\nhe\r\n3\r\nl", 101)
val second = async_proxy_prepare_client_chunk(first, "lo\r\n0\r\n\r\n", 102)
expect(first.response_headers_done).to_be(true)
expect(first.pending_client_data).to_contain("Content-Type: text/plain\r\n")
expect(first.pending_client_data).to_end_with("\r\n\r\nhe")
expect(first.chunked_body_buffer).to_equal("3\r\nl")
expect(first.body_bytes_forwarded).to_equal(2)
expect(async_proxy_response_complete(first)).to_be(false)
expect(async_proxy_response_complete(second)).to_be(true)
expect(second.pending_client_data).to_equal("llo")
expect(second.body_bytes_forwarded).to_equal(5)
```

</details>

#### should reject chunked body buffering over response budget

- Fail closed before an incomplete chunked body grows without bound
   - Expected: rejected.response_header_error equals `Proxy upstream chunked response buffer too large`
   - Expected: rejected.pending_client_data equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Fail closed before an incomplete chunked body grows without bound")
val conn = async_proxy_connection_with_limits(
    10,
    "127.0.0.1:3000",
    "GET / HTTP/1.1\r\n\r\n",
    100,
    1024,
    4,
    1000,
    30000
)
val rejected = async_proxy_prepare_client_chunk(conn, "HTTP/1.1 200 OK\r\nTransfer-Encoding: chunked\r\n\r\n5\r\nhello", 101)
expect(rejected.response_header_valid).to_be(false)
expect(rejected.response_header_error).to_equal("Proxy upstream chunked response buffer too large")
expect(rejected.pending_client_data).to_equal("")
```

</details>

#### should reject later chunked buffering over response budget

- Apply the same buffer budget after response headers are complete
   - Expected: rejected.response_header_error equals `Proxy upstream chunked response buffer too large`


<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Apply the same buffer budget after response headers are complete")
val conn = async_proxy_connection_with_limits(
    10,
    "127.0.0.1:3000",
    "GET / HTTP/1.1\r\n\r\n",
    100,
    1024,
    7,
    1000,
    30000
)
val first = async_proxy_prepare_client_chunk(conn, "HTTP/1.1 200 OK\r\nTransfer-Encoding: chunked\r\n\r\n5\r\nhe", 101)
val rejected = async_proxy_prepare_client_chunk(first, "llo", 102)
expect(first.response_header_valid).to_be(true)
expect(rejected.response_header_valid).to_be(false)
expect(rejected.response_header_error).to_equal("Proxy upstream chunked response buffer too large")
```

</details>

#### should parse upstream response content length

- Extract response body length from end-to-end headers
   - Expected: async_proxy_content_length("HTTP/1.1 200 OK\r\nContent-Length: 5") equals `5`
   - Expected: async_proxy_content_length("HTTP/1.1 200 OK\r\ncontent-length: 0") equals `0`
   - Expected: async_proxy_content_length("HTTP/1.1 200 OK\r\nContent-Type: text/plain") equals `-1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Extract response body length from end-to-end headers")
expect(async_proxy_content_length("HTTP/1.1 200 OK\r\nContent-Length: 5")).to_equal(5)
expect(async_proxy_content_length("HTTP/1.1 200 OK\r\ncontent-length: 0")).to_equal(0)
expect(async_proxy_content_length("HTTP/1.1 200 OK\r\nContent-Type: text/plain")).to_equal(-1)
```

</details>

#### should validate upstream response status lines

- Reject malformed upstream status before client send


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Reject malformed upstream status before client send")
expect(async_proxy_status_line_valid("HTTP/1.1 200 OK")).to_be(true)
expect(async_proxy_status_line_valid("HTTP/1.1 999 Bad")).to_be(false)
expect(async_proxy_status_line_valid("OK 200")).to_be(false)
```

</details>

#### should reject malformed upstream response headers

- Validate header syntax, line length, and count budgets
   - Expected: malformed.reason equals `Proxy upstream response header malformed`
   - Expected: too_many.reason equals `Proxy upstream response header count exceeded`
   - Expected: too_long.reason equals `Proxy upstream status line too large`


<details>
<summary>Executable SSpec</summary>

Runnable source: 22 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Validate header syntax, line length, and count budgets")
val malformed = async_proxy_validate_response_headers(
    "HTTP/1.1 200 OK\r\nbad header",
    8192,
    100
)
val too_many = async_proxy_validate_response_headers(
    "HTTP/1.1 200 OK\r\nA: 1\r\nB: 2",
    8192,
    1
)
val too_long = async_proxy_validate_response_headers(
    "HTTP/1.1 200 OK\r\nX-Long: abcdef",
    8,
    100
)
expect(malformed.ok).to_be(false)
expect(malformed.reason).to_equal("Proxy upstream response header malformed")
expect(too_many.ok).to_be(false)
expect(too_many.reason).to_equal("Proxy upstream response header count exceeded")
expect(too_long.ok).to_be(false)
expect(too_long.reason).to_equal("Proxy upstream status line too large")
```

</details>

#### should reject ambiguous upstream response body framing

- Fail closed before rewriting Content-Length plus Transfer-Encoding
   - Expected: validation.reason equals `Proxy upstream response framing conflict`
   - Expected: rejected.response_header_error equals `Proxy upstream response framing conflict`


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Fail closed before rewriting Content-Length plus Transfer-Encoding")
val validation = async_proxy_validate_response_headers(
    "HTTP/1.1 200 OK\r\nContent-Length: 5\r\nTransfer-Encoding: chunked",
    8192,
    100
)
val conn = async_proxy_connection(10, "127.0.0.1:3000", "GET / HTTP/1.1\r\n\r\n", 100)
val rejected = async_proxy_prepare_client_chunk(conn, "HTTP/1.1 200 OK\r\nContent-Length: 5\r\nTransfer-Encoding: chunked\r\n\r\n0\r\n\r\n", 101)
expect(async_proxy_response_framing_conflict("HTTP/1.1 200 OK\r\nContent-Length: 5\r\nTransfer-Encoding: chunked")).to_be(true)
expect(validation.ok).to_be(false)
expect(validation.reason).to_equal("Proxy upstream response framing conflict")
expect(rejected.response_header_valid).to_be(false)
expect(rejected.response_header_error).to_equal("Proxy upstream response framing conflict")
```

</details>

#### should reject invalid or conflicting upstream response content lengths

- Fail closed before trusting ambiguous response body length
   - Expected: invalid.reason equals `Proxy upstream response content length invalid`
   - Expected: mismatch.reason equals `Proxy upstream response content length conflict`
   - Expected: rejected.response_header_error equals `Proxy upstream response content length conflict`


<details>
<summary>Executable SSpec</summary>

Runnable source: 26 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Fail closed before trusting ambiguous response body length")
val invalid = async_proxy_validate_response_headers(
    "HTTP/1.1 200 OK\r\nContent-Length: nope",
    8192,
    100
)
val mismatch = async_proxy_validate_response_headers(
    "HTTP/1.1 200 OK\r\nContent-Length: 5\r\nContent-Length: 7",
    8192,
    100
)
val duplicate = async_proxy_validate_response_headers(
    "HTTP/1.1 200 OK\r\nContent-Length: 5\r\nContent-Length: 5",
    8192,
    100
)
val conn = async_proxy_connection(10, "127.0.0.1:3000", "GET / HTTP/1.1\r\n\r\n", 100)
val rejected = async_proxy_prepare_client_chunk(conn, "HTTP/1.1 200 OK\r\nContent-Length: 5\r\nContent-Length: 7\r\n\r\nhello", 101)
expect(async_proxy_response_content_length_invalid("HTTP/1.1 200 OK\r\nContent-Length: nope")).to_be(true)
expect(async_proxy_response_content_length_conflict("HTTP/1.1 200 OK\r\nContent-Length: 5\r\nContent-Length: 7")).to_be(true)
expect(async_proxy_response_content_length_conflict("HTTP/1.1 200 OK\r\nContent-Length: 5\r\nContent-Length: 5")).to_be(false)
expect(invalid.reason).to_equal("Proxy upstream response content length invalid")
expect(mismatch.reason).to_equal("Proxy upstream response content length conflict")
expect(duplicate.ok).to_be(true)
expect(rejected.response_header_valid).to_be(false)
expect(rejected.response_header_error).to_equal("Proxy upstream response content length conflict")
```

</details>

#### should reject unsupported upstream response transfer encodings

- Do not strip an unknown Transfer-Encoding and forward changed body semantics
   - Expected: validation.reason equals `Proxy upstream transfer encoding unsupported`
   - Expected: mixed.reason equals `Proxy upstream transfer encoding unsupported`


<details>
<summary>Executable SSpec</summary>

Runnable source: 20 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Do not strip an unknown Transfer-Encoding and forward changed body semantics")
val validation = async_proxy_validate_response_headers(
    "HTTP/1.1 200 OK\r\nTransfer-Encoding: gzip",
    8192,
    100
)
val mixed = async_proxy_validate_response_headers(
    "HTTP/1.1 200 OK\r\nTransfer-Encoding: gzip, chunked",
    8192,
    100
)
expect(async_proxy_response_has_transfer_encoding("HTTP/1.1 200 OK\r\nTransfer-Encoding: gzip")).to_be(true)
expect(async_proxy_transfer_chunked("HTTP/1.1 200 OK\r\nTransfer-Encoding: gzip")).to_be(false)
expect(async_proxy_response_unsupported_transfer_encoding("HTTP/1.1 200 OK\r\nTransfer-Encoding: gzip")).to_be(true)
expect(validation.ok).to_be(false)
expect(validation.reason).to_equal("Proxy upstream transfer encoding unsupported")
expect(async_proxy_transfer_chunked("HTTP/1.1 200 OK\r\nTransfer-Encoding: gzip, chunked")).to_be(true)
expect(async_proxy_response_unsupported_transfer_encoding("HTTP/1.1 200 OK\r\nTransfer-Encoding: gzip, chunked")).to_be(true)
expect(mixed.ok).to_be(false)
expect(mixed.reason).to_equal("Proxy upstream transfer encoding unsupported")
```

</details>

#### should buffer partial upstream response headers until complete

- Hold incomplete headers in proxy state instead of sending malformed data
   - Expected: partial.pending_client_data equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Hold incomplete headers in proxy state instead of sending malformed data")
val conn = async_proxy_connection(10, "127.0.0.1:3000", "GET / HTTP/1.1\r\n\r\n", 100)
val partial = async_proxy_prepare_client_chunk(conn, "HTTP/1.1 200 OK\r\nContent-Type: text/plain", 101)
expect(partial.response_headers_done).to_be(false)
expect(partial.pending_client_data).to_equal("")
val complete = async_proxy_prepare_client_chunk(partial, "\r\n\r\nhello", 102)
expect(complete.response_headers_done).to_be(true)
expect(complete.pending_client_data).to_contain("HTTP/1.1 200 OK\r\n")
expect(complete.pending_client_data).to_contain("Content-Type: text/plain\r\n")
expect(complete.pending_client_data).to_end_with("\r\n\r\nhello")
```

</details>

#### should mark content-length responses complete when body arrives with headers

- Complete response framing without requiring upstream EOF
   - Expected: complete.expected_body_bytes equals `5`
   - Expected: complete.body_bytes_forwarded equals `5`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Complete response framing without requiring upstream EOF")
val conn = async_proxy_connection(10, "127.0.0.1:3000", "GET / HTTP/1.1\r\n\r\n", 100)
val complete = async_proxy_prepare_client_chunk(conn, "HTTP/1.1 200 OK\r\nContent-Length: 5\r\n\r\nhello", 101)
expect(complete.expected_body_bytes).to_equal(5)
expect(complete.body_bytes_forwarded).to_equal(5)
expect(async_proxy_response_complete(complete)).to_be(true)
expect(async_proxy_response_reusable(complete)).to_be(true)
expect(complete.pending_client_data).to_end_with("\r\n\r\nhello")
```

</details>

#### should mark no-body status responses complete at header completion

- Do not wait for upstream EOF on 204 responses
   - Expected: async_proxy_status_code("HTTP/1.1 204 No Content") equals `204`
   - Expected: complete.expected_body_bytes equals `0`
   - Expected: complete.body_bytes_forwarded equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Do not wait for upstream EOF on 204 responses")
val conn = async_proxy_connection(10, "127.0.0.1:3000", "GET / HTTP/1.1\r\n\r\n", 100)
val complete = async_proxy_prepare_client_chunk(conn, "HTTP/1.1 204 No Content\r\nContent-Length: 99\r\n\r\n", 101)
expect(async_proxy_status_code("HTTP/1.1 204 No Content")).to_equal(204)
expect(async_proxy_response_has_no_body("HTTP/1.1 204 No Content\r\nContent-Length: 99")).to_be(true)
expect(complete.expected_body_bytes).to_equal(0)
expect(complete.body_bytes_forwarded).to_equal(0)
expect(async_proxy_response_complete(complete)).to_be(true)
expect(async_proxy_response_reusable(complete)).to_be(true)
expect(complete.pending_client_data).to_start_with("HTTP/1.1 204 No Content\r\n")
expect(complete.pending_client_data).to_end_with("\r\n\r\n")
```

</details>

#### should not forward accidental upstream body bytes for no-body statuses

- Protect clients and pooled fds when an upstream sends invalid 304 body bytes
   - Expected: complete.expected_body_bytes equals `0`
   - Expected: complete.body_bytes_forwarded equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Protect clients and pooled fds when an upstream sends invalid 304 body bytes")
val conn = async_proxy_connection(10, "127.0.0.1:3000", "GET /cached HTTP/1.1\r\n\r\n", 100)
val complete = async_proxy_prepare_client_chunk(conn, "HTTP/1.1 304 Not Modified\r\nContent-Length: 5\r\n\r\nhello", 101)
expect(async_proxy_response_has_no_body("HTTP/1.1 304 Not Modified\r\nContent-Length: 5")).to_be(true)
expect(complete.expected_body_bytes).to_equal(0)
expect(complete.body_bytes_forwarded).to_equal(0)
expect(async_proxy_response_complete(complete)).to_be(true)
expect(async_proxy_response_reusable(complete)).to_be(false)
expect(complete.pending_client_data.contains("hello")).to_be(false)
```

</details>

#### should reject oversized declared content length before reading body

- Fail closed when upstream declares a body larger than proxy budget
   - Expected: rejected.response_header_error equals `Proxy upstream response content length too large`
   - Expected: rejected.pending_client_data equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Fail closed when upstream declares a body larger than proxy budget")
val conn = async_proxy_connection_with_limits(
    10,
    "127.0.0.1:3000",
    "GET / HTTP/1.1\r\n\r\n",
    100,
    1024,
    4,
    1000,
    30000
)
val rejected = async_proxy_prepare_client_chunk(conn, "HTTP/1.1 200 OK\r\nContent-Length: 5\r\n\r\n", 101)
expect(rejected.response_header_valid).to_be(false)
expect(rejected.response_header_error).to_equal("Proxy upstream response content length too large")
expect(rejected.pending_client_data).to_equal("")
```

</details>

#### should allow declared content length within response budget

- Keep framed responses valid when Content-Length fits the budget


<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Keep framed responses valid when Content-Length fits the budget")
val conn = async_proxy_connection_with_limits(
    10,
    "127.0.0.1:3000",
    "GET / HTTP/1.1\r\n\r\n",
    100,
    1024,
    5,
    1000,
    30000
)
val complete = async_proxy_prepare_client_chunk(conn, "HTTP/1.1 200 OK\r\nContent-Length: 5\r\n\r\nhello", 101)
expect(complete.response_header_valid).to_be(true)
expect(async_proxy_response_complete(complete)).to_be(true)
expect(async_proxy_response_reusable(complete)).to_be(true)
expect(complete.pending_client_data).to_end_with("\r\n\r\nhello")
```

</details>

#### should not reuse upstream responses that ask to close

- Keep the fd pool from retaining a framed but non-reusable backend socket


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Keep the fd pool from retaining a framed but non-reusable backend socket")
val conn = async_proxy_connection(10, "127.0.0.1:3000", "GET / HTTP/1.1\r\n\r\n", 100)
val complete = async_proxy_prepare_client_chunk(conn, "HTTP/1.1 200 OK\r\nConnection: close\r\nContent-Length: 5\r\n\r\nhello", 101)
expect(async_proxy_response_allows_reuse("HTTP/1.1 200 OK\r\nConnection: close\r\nContent-Length: 5")).to_be(false)
expect(async_proxy_response_complete(complete)).to_be(true)
expect(async_proxy_response_reusable(complete)).to_be(false)
```

</details>

#### should parse upstream close reuse tokens without substring matches

- Only a real Connection close token disables upstream fd reuse


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Only a real Connection close token disables upstream fd reuse")
expect(async_proxy_response_allows_reuse("HTTP/1.1 200 OK\r\nConnection: keep-alive, close\r\nContent-Length: 5")).to_be(false)
expect(async_proxy_response_allows_reuse("HTTP/1.1 200 OK\r\nConnection: enclose\r\nContent-Length: 5")).to_be(true)
```

</details>

#### should mark content-length responses complete across later body chunks

- Accumulate body bytes after completed headers
   - Expected: first.body_bytes_forwarded equals `2`
   - Expected: second.body_bytes_forwarded equals `5`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Accumulate body bytes after completed headers")
val conn = async_proxy_connection(10, "127.0.0.1:3000", "GET / HTTP/1.1\r\n\r\n", 100)
val first = async_proxy_prepare_client_chunk(conn, "HTTP/1.1 200 OK\r\nContent-Length: 5\r\n\r\nhe", 101)
val second = async_proxy_prepare_client_chunk(first, "llo", 102)
expect(first.response_headers_done).to_be(true)
expect(first.body_bytes_forwarded).to_equal(2)
expect(async_proxy_response_complete(first)).to_be(false)
expect(second.body_bytes_forwarded).to_equal(5)
expect(async_proxy_response_complete(second)).to_be(true)
```

</details>

#### should mark completed malformed headers invalid without client data

- Hold invalid completed headers for worker error handling
   - Expected: invalid.response_header_error equals `Proxy upstream response header malformed`
   - Expected: invalid.pending_client_data equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Hold invalid completed headers for worker error handling")
val conn = async_proxy_connection(10, "127.0.0.1:3000", "GET / HTTP/1.1\r\n\r\n", 100)
val invalid = async_proxy_prepare_client_chunk(conn, "HTTP/1.1 200 OK\r\nbad header\r\n\r\nbody", 101)
expect(invalid.response_header_valid).to_be(false)
expect(invalid.response_header_error).to_equal("Proxy upstream response header malformed")
expect(invalid.pending_client_data).to_equal("")
```

</details>

#### should keep tunnel setup wire pending across partial upstream writes

- Preserve unsent WebSocket upgrade bytes until the upstream setup write completes
   - Expected: async_proxy_tunnel_setup_remaining(conn) equals `setup`
   - Expected: async_proxy_tunnel_setup_remaining(complete) equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Preserve unsent WebSocket upgrade bytes until the upstream setup write completes")
val setup = "GET /chat HTTP/1.1\r\nHost: 127.0.0.1:3000\r\nConnection: Upgrade\r\nUpgrade: websocket\r\n\r\n"
val conn = async_proxy_tunnel_connection(10, 20, "127.0.0.1:3000", "upgrade", setup, 100)
val first = async_proxy_tunnel_mark_setup_sent(conn, 24, 101)
val complete = async_proxy_tunnel_mark_setup_sent(first, 4096, 102)
expect(async_proxy_tunnel_setup_remaining(conn)).to_equal(setup)
expect(async_proxy_tunnel_setup_complete(conn)).to_be(false)
expect(async_proxy_tunnel_setup_remaining(first)).to_start_with("Host: 127.0.0.1:3000")
expect(async_proxy_tunnel_setup_complete(first)).to_be(false)
expect(async_proxy_tunnel_setup_remaining(complete)).to_equal("")
expect(async_proxy_tunnel_setup_complete(complete)).to_be(true)
```

</details>

#### should validate upstream 101 responses before upgrade tunnel relay

- Wait for a valid Switching Protocols response before relaying client frames
   - Expected: prepared.pending_upstream_to_client equals `response`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Wait for a valid Switching Protocols response before relaying client frames")
val conn = async_proxy_tunnel_connection(10, 20, "127.0.0.1:3000", "upgrade", "", 100)
val response = "HTTP/1.1 101 Switching Protocols\r\nConnection: Upgrade\r\nUpgrade: websocket\r\n\r\n"
val prepared = async_proxy_tunnel_prepare_upstream_handshake(conn, response, [], 101)
expect(conn.upstream_handshake_complete).to_be(false)
expect(async_proxy_tunnel_should_recv_client(conn)).to_be(false)
expect(prepared.upstream_handshake_complete).to_be(true)
expect(prepared.upstream_handshake_valid).to_be(true)
expect(prepared.pending_upstream_to_client).to_equal(response)
```

</details>

#### should validate live fixture upstream 101 responses before tunnel relay

- Accept the same Switching Protocols response shape used by the live tunnel fixture
   - Expected: prepared.pending_upstream_to_client equals `response`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Accept the same Switching Protocols response shape used by the live tunnel fixture")
val conn = async_proxy_tunnel_connection(10, 20, "127.0.0.1:3000", "upgrade", "", 100)
val response = "HTTP/1.1 101 Switching Protocols\r\nUpgrade: websocket\r\nConnection: Upgrade\r\nX-Tunnel-Fixture: yes\r\n\r\n"
val prepared = async_proxy_tunnel_prepare_upstream_handshake(conn, response, [], 101)
expect(prepared.upstream_handshake_complete).to_be(true)
expect(prepared.upstream_handshake_valid).to_be(true)
expect(prepared.pending_upstream_to_client).to_equal(response)
```

</details>

#### should validate LF-normalized upstream 101 responses before tunnel relay

- Accept runtime-normalized line endings while preserving Upgrade validation


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Accept runtime-normalized line endings while preserving Upgrade validation")
val conn = async_proxy_tunnel_connection(10, 20, "127.0.0.1:3000", "upgrade", "", 100)
val response = "HTTP/1.1 101 Switching Protocols\nUpgrade: websocket\nConnection: Upgrade\nX-Tunnel-Fixture: yes\n\n"
val prepared = async_proxy_tunnel_prepare_upstream_handshake(conn, response, [], 101)
expect(prepared.upstream_handshake_complete).to_be(true)
expect(prepared.upstream_handshake_valid).to_be(true)
```

</details>

#### should reject invalid upstream upgrade tunnel responses

- Fail closed when upstream does not confirm Switching Protocols
- async proxy tunnel connection
- async proxy tunnel connection
- async proxy tunnel connection
- async proxy tunnel connection
   - Expected: ok_status_missing_connection.upstream_handshake_error equals `Proxy tunnel upstream upgrade response invalid`
   - Expected: wrong_status.upstream_handshake_error equals `Proxy tunnel upstream upgrade response invalid`


<details>
<summary>Executable SSpec</summary>

Runnable source: 31 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Fail closed when upstream does not confirm Switching Protocols")
val ok_status_missing_connection = async_proxy_tunnel_prepare_upstream_handshake(
    async_proxy_tunnel_connection(10, 20, "127.0.0.1:3000", "upgrade", "", 100),
    "HTTP/1.1 101 Switching Protocols\r\nUpgrade: websocket\r\n\r\n",
    [],
    101
)
val wrong_status = async_proxy_tunnel_prepare_upstream_handshake(
    async_proxy_tunnel_connection(10, 20, "127.0.0.1:3000", "upgrade", "", 100),
    "HTTP/1.1 200 OK\r\nConnection: Upgrade\r\nUpgrade: websocket\r\n\r\n",
    [],
    102
)
val missing_upgrade = async_proxy_tunnel_prepare_upstream_handshake(
    async_proxy_tunnel_connection(10, 20, "127.0.0.1:3000", "upgrade", "", 100),
    "HTTP/1.1 101 Switching Protocols\r\nConnection: Upgrade\r\n\r\n",
    [],
    103
)
val empty_upgrade = async_proxy_tunnel_prepare_upstream_handshake(
    async_proxy_tunnel_connection(10, 20, "127.0.0.1:3000", "upgrade", "", 100),
    "HTTP/1.1 101 Switching Protocols\r\nConnection: Upgrade\r\nUpgrade: \r\n\r\n",
    [],
    104
)
expect(ok_status_missing_connection.upstream_handshake_valid).to_be(false)
expect(ok_status_missing_connection.upstream_handshake_error).to_equal("Proxy tunnel upstream upgrade response invalid")
expect(wrong_status.upstream_handshake_valid).to_be(false)
expect(wrong_status.upstream_handshake_error).to_equal("Proxy tunnel upstream upgrade response invalid")
expect(missing_upgrade.upstream_handshake_valid).to_be(false)
expect(empty_upgrade.upstream_handshake_valid).to_be(false)
```

</details>

#### should accept comma-token upgrade connection headers

- Treat Connection tokens case-insensitively without accepting substring matches
- async proxy tunnel connection
- async proxy tunnel connection


<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Treat Connection tokens case-insensitively without accepting substring matches")
val comma_token = async_proxy_tunnel_prepare_upstream_handshake(
    async_proxy_tunnel_connection(10, 20, "127.0.0.1:3000", "upgrade", "", 100),
    "HTTP/1.1 101 Switching Protocols\r\nConnection: keep-alive, UpGrAdE\r\nUpgrade: websocket\r\n\r\n",
    [],
    101
)
val substring_only = async_proxy_tunnel_prepare_upstream_handshake(
    async_proxy_tunnel_connection(10, 20, "127.0.0.1:3000", "upgrade", "", 100),
    "HTTP/1.1 101 Switching Protocols\r\nConnection: xupgrade\r\nUpgrade: websocket\r\n\r\n",
    [],
    102
)
expect(comma_token.upstream_handshake_valid).to_be(true)
expect(comma_token.upstream_handshake_complete).to_be(true)
expect(substring_only.upstream_handshake_valid).to_be(false)
```

</details>

#### should buffer tunnel relay data independently in both directions

- Let worker I/O drain client-to-upstream and upstream-to-client buffers separately
   - Expected: queued_both.pending_client_to_upstream equals `client-frame`
   - Expected: queued_both.pending_upstream_to_client equals `server-frame`
   - Expected: queued_both.bytes_client_to_upstream equals `12`
   - Expected: queued_both.bytes_upstream_to_client equals `12`
   - Expected: client_partial.pending_client_to_upstream equals `-frame`
   - Expected: server_drained.pending_upstream_to_client equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 17 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Let worker I/O drain client-to-upstream and upstream-to-client buffers separately")
val conn = async_proxy_tunnel_connection(10, 20, "127.0.0.1:3000", "upgrade", "", 100)
val queued_client = async_proxy_tunnel_queue_client_data(conn, "client-frame", 101)
val queued_both = async_proxy_tunnel_queue_upstream_data(queued_client, "server-frame", 102)
val client_partial = async_proxy_tunnel_mark_client_data_sent(queued_both, 6, 103)
val server_drained = async_proxy_tunnel_mark_upstream_data_sent(client_partial, 4096, 104)
expect(async_proxy_tunnel_should_recv_client(conn)).to_be(false)
expect(async_proxy_tunnel_should_recv_upstream(conn)).to_be(true)
expect(queued_both.pending_client_to_upstream).to_equal("client-frame")
expect(queued_both.pending_upstream_to_client).to_equal("server-frame")
expect(queued_both.bytes_client_to_upstream).to_equal(12)
expect(queued_both.bytes_upstream_to_client).to_equal(12)
expect(async_proxy_tunnel_should_recv_client(queued_both)).to_be(false)
expect(async_proxy_tunnel_should_recv_upstream(queued_both)).to_be(false)
expect(client_partial.pending_client_to_upstream).to_equal("-frame")
expect(server_drained.pending_upstream_to_client).to_equal("")
expect(async_proxy_tunnel_should_recv_upstream(server_drained)).to_be(true)
```

</details>

#### should suppress duplicate tunnel reads while a direction has an in-flight recv

- Track worker-submitted recv operations so a drained send does not schedule a second read on the same fd
- var conn = async proxy tunnel connection


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Track worker-submitted recv operations so a drained send does not schedule a second read on the same fd")
var conn = async_proxy_tunnel_connection(10, 20, "127.0.0.1:3000", "upgrade", "", 100)
expect(async_proxy_tunnel_should_recv_client(conn)).to_be(false)
expect(async_proxy_tunnel_should_recv_upstream(conn)).to_be(true)
conn.client_recv_inflight = true
conn.upstream_recv_inflight = true
expect(async_proxy_tunnel_should_recv_client(conn)).to_be(false)
expect(async_proxy_tunnel_should_recv_upstream(conn)).to_be(false)
```

</details>

#### should preserve binary tunnel payloads across partial sends

- Use byte buffers for raw WebSocket and CONNECT relay data after HTTP setup
   - Expected: queued.pending_client_to_upstream_bytes.len() equals `4`
   - Expected: queued.pending_client_to_upstream_bytes[0] equals `0`
   - Expected: queued.pending_client_to_upstream_bytes[1] equals `255`
   - Expected: partial.pending_client_to_upstream_bytes.len() equals `2`
   - Expected: partial.pending_client_to_upstream_bytes[0] equals `65`
   - Expected: upstream.pending_upstream_to_client_bytes.len() equals `3`
   - Expected: upstream_drained.pending_upstream_to_client_bytes.len() equals `2`
   - Expected: upstream_drained.pending_upstream_to_client_bytes[0] equals `0`
   - Expected: upstream_drained.pending_upstream_to_client_bytes[1] equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Use byte buffers for raw WebSocket and CONNECT relay data after HTTP setup")
val conn = async_proxy_tunnel_connection(10, 20, "127.0.0.1:3000", "upgrade", "", 100)
val queued = async_proxy_tunnel_queue_client_bytes(conn, [0, 255, 65, 66], 101)
val partial = async_proxy_tunnel_mark_client_data_sent(queued, 2, 102)
val upstream = async_proxy_tunnel_queue_upstream_bytes(partial, [128, 0, 1], 103)
val upstream_drained = async_proxy_tunnel_mark_upstream_data_sent(upstream, 1, 104)
expect(queued.pending_client_to_upstream_bytes.len()).to_equal(4)
expect(queued.pending_client_to_upstream_bytes[0]).to_equal(0)
expect(queued.pending_client_to_upstream_bytes[1]).to_equal(255)
expect(partial.pending_client_to_upstream_bytes.len()).to_equal(2)
expect(partial.pending_client_to_upstream_bytes[0]).to_equal(65)
expect(upstream.pending_upstream_to_client_bytes.len()).to_equal(3)
expect(upstream_drained.pending_upstream_to_client_bytes.len()).to_equal(2)
expect(upstream_drained.pending_upstream_to_client_bytes[0]).to_equal(0)
expect(upstream_drained.pending_upstream_to_client_bytes[1]).to_equal(1)
```

</details>

#### should preserve client bytes coalesced after upgrade request headers

- Keep raw payload bytes that arrive in the same recv as the HTTP upgrade headers
- var conn = Connection new
   - Expected: carried.len() equals `2`
   - Expected: "unexpected" equals `request-ready`
   - Expected: carried[0] equals `129`
   - Expected: carried[1] equals `5`
   - Expected: conn.drain_pending_tunnel_bytes().len() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Keep raw payload bytes that arrive in the same recv as the HTTP upgrade headers")
var conn = Connection.new(10, "10.0.0.8", 100)
val wire = "GET /chat HTTP/1.1\r\nHost: example\r\nConnection: Upgrade\r\nUpgrade: websocket\r\n\r\n"
val raw = [71, 69, 84, 32, 47, 99, 104, 97, 116, 32, 72, 84, 84, 80, 47, 49, 46, 49, 13, 10, 72, 111, 115, 116, 58, 32, 101, 120, 97, 109, 112, 108, 101, 13, 10, 67, 111, 110, 110, 101, 99, 116, 105, 111, 110, 58, 32, 85, 112, 103, 114, 97, 100, 101, 13, 10, 85, 112, 103, 114, 97, 100, 101, 58, 32, 119, 101, 98, 115, 111, 99, 107, 101, 116, 13, 10, 13, 10, 129, 5]
val action = conn.on_data_received_bytes("{wire}AA", raw, 101)
val carried = conn.drain_pending_tunnel_bytes()
match action:
    ConnectionAction.RequestReady:
        expect(carried.len()).to_equal(2)
    _:
        expect("unexpected").to_equal("request-ready")
expect(carried[0]).to_equal(129)
expect(carried[1]).to_equal(5)
expect(conn.drain_pending_tunnel_bytes().len()).to_equal(0)
```

</details>

#### should validate upstream 101 before opening an upgrade tunnel

- Forward the upstream switching-protocol response before allowing raw client relay
   - Expected: prepared.pending_upstream_to_client equals ``
   - Expected: prepared.pending_upstream_to_client_bytes.len() equals `response.len()`
   - Expected: prepared.pending_upstream_to_client_bytes[0] equals `72`


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Forward the upstream switching-protocol response before allowing raw client relay")
val conn = async_proxy_tunnel_connection(10, 20, "127.0.0.1:3000", "upgrade", "", 100)
val response = "HTTP/1.1 101 Switching Protocols\r\nUpgrade: websocket\r\nConnection: Upgrade\r\n\r\n"
val prepared = async_proxy_tunnel_prepare_upstream_handshake(conn, response, [72, 84, 84, 80, 47, 49, 46, 49, 32, 49, 48, 49, 32, 83, 119, 105, 116, 99, 104, 105, 110, 103, 32, 80, 114, 111, 116, 111, 99, 111, 108, 115, 13, 10, 85, 112, 103, 114, 97, 100, 101, 58, 32, 119, 101, 98, 115, 111, 99, 107, 101, 116, 13, 10, 67, 111, 110, 110, 101, 99, 116, 105, 111, 110, 58, 32, 85, 112, 103, 114, 97, 100, 101, 13, 10, 13, 10], 101)
expect(prepared.upstream_handshake_valid).to_be(true)
expect(prepared.upstream_handshake_complete).to_be(true)
expect(prepared.pending_upstream_to_client).to_equal("")
expect(prepared.pending_upstream_to_client_bytes.len()).to_equal(response.len())
expect(prepared.pending_upstream_to_client_bytes[0]).to_equal(72)
expect(async_proxy_tunnel_should_recv_client(prepared)).to_be(false)
val drained = async_proxy_tunnel_mark_upstream_data_sent(prepared, response.len(), 102)
expect(async_proxy_tunnel_should_recv_client(drained)).to_be(true)
```

</details>

#### should reject non-101 upstream upgrade responses

- Fail closed before raw client bytes can be relayed to a backend that refused upgrade
   - Expected: prepared.upstream_handshake_error equals `Proxy tunnel upstream upgrade response invalid`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Fail closed before raw client bytes can be relayed to a backend that refused upgrade")
val conn = async_proxy_tunnel_connection(10, 20, "127.0.0.1:3000", "upgrade", "", 100)
val response = "HTTP/1.1 200 OK\r\nContent-Length: 0\r\n\r\n"
val prepared = async_proxy_tunnel_prepare_upstream_handshake(conn, response, [72, 84, 84, 80, 47, 49, 46, 49, 32, 50, 48, 48, 32, 79, 75, 13, 10, 67, 111, 110, 116, 101, 110, 116, 45, 76, 101, 110, 103, 116, 104, 58, 32, 48, 13, 10, 13, 10], 101)
expect(prepared.upstream_handshake_valid).to_be(false)
expect(prepared.upstream_handshake_error).to_equal("Proxy tunnel upstream upgrade response invalid")
expect(async_proxy_tunnel_should_recv_client(prepared)).to_be(false)
```

</details>

#### should fall back to text delimiter detection for native tunnel upgrade reads

- Complete the 101 handshake when native raw bytes are present but text carries the reliable header boundary
   - Expected: prepared.pending_upstream_to_client equals `response`
   - Expected: prepared.pending_upstream_to_client_bytes.len() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Complete the 101 handshake when native raw bytes are present but text carries the reliable header boundary")
val conn = async_proxy_tunnel_connection(10, 20, "127.0.0.1:3000", "upgrade", "", 100)
val response = "HTTP/1.1 101 Switching Protocols\r\nUpgrade: websocket\r\nConnection: Upgrade\r\n\r\n"
val prepared = async_proxy_tunnel_prepare_upstream_handshake(conn, response, [1, 2, 3], 101)
expect(prepared.upstream_handshake_valid).to_be(true)
expect(prepared.upstream_handshake_complete).to_be(true)
expect(prepared.pending_upstream_to_client).to_equal(response)
expect(prepared.pending_upstream_to_client_bytes.len()).to_equal(0)
```

</details>

#### should preserve bytes after split upstream upgrade headers

- Keep the first tunneled payload bytes when they arrive with the terminating 101 header fragment
   - Expected: second.pending_upstream_to_client equals ``
   - Expected: second.pending_upstream_to_client_bytes[0] equals `72`
   - Expected: second.pending_upstream_to_client_bytes[second.pending_upstream_to_client_bytes.len() - 2] equals `129`
   - Expected: second.pending_upstream_to_client_bytes[second.pending_upstream_to_client_bytes.len() - 1] equals `5`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Keep the first tunneled payload bytes when they arrive with the terminating 101 header fragment")
val conn = async_proxy_tunnel_connection(10, 20, "127.0.0.1:3000", "upgrade", "", 100)
val first = async_proxy_tunnel_prepare_upstream_handshake(conn, "HTTP/1.1 101 Switching Protocols\r\nUpgrade: websocket\r\n", [72, 84, 84, 80, 47, 49, 46, 49, 32, 49, 48, 49, 32, 83, 119, 105, 116, 99, 104, 105, 110, 103, 32, 80, 114, 111, 116, 111, 99, 111, 108, 115, 13, 10, 85, 112, 103, 114, 97, 100, 101, 58, 32, 119, 101, 98, 115, 111, 99, 107, 101, 116, 13, 10], 101)
val second_text = "Connection: Upgrade\r\n\r\n"
val second = async_proxy_tunnel_prepare_upstream_handshake(first, second_text, [67, 111, 110, 110, 101, 99, 116, 105, 111, 110, 58, 32, 85, 112, 103, 114, 97, 100, 101, 13, 10, 13, 10, 129, 5], 102)
expect(first.upstream_handshake_complete).to_be(false)
expect(second.upstream_handshake_complete).to_be(true)
expect(second.pending_upstream_to_client).to_equal("")
expect(second.pending_upstream_to_client_bytes[0]).to_equal(72)
expect(second.pending_upstream_to_client_bytes[second.pending_upstream_to_client_bytes.len() - 2]).to_equal(129)
expect(second.pending_upstream_to_client_bytes[second.pending_upstream_to_client_bytes.len() - 1]).to_equal(5)
```

</details>

#### should reject tunnel buffering over per-direction backpressure budget

- Fail closed when either tunnel relay direction exceeds the configured pending byte cap


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Fail closed when either tunnel relay direction exceeds the configured pending byte cap")
val conn = async_proxy_tunnel_connection_with_limit(10, 20, "127.0.0.1:3000", "upgrade", "", 100, 4)
val ok = async_proxy_tunnel_queue_client_data(conn, "abcd", 101)
val over_client = async_proxy_tunnel_queue_client_data(ok, "e", 102)
val over_upstream = async_proxy_tunnel_queue_upstream_data(conn, "abcde", 103)
val over_binary = async_proxy_tunnel_queue_client_bytes(conn, [1, 2, 3, 4, 5], 104)
val closed = async_proxy_tunnel_mark_closed(over_client, 104)
expect(async_proxy_tunnel_pending_over_budget(ok)).to_be(false)
expect(async_proxy_tunnel_pending_over_budget(over_client)).to_be(true)
expect(async_proxy_tunnel_pending_over_budget(over_upstream)).to_be(true)
expect(async_proxy_tunnel_pending_over_budget(over_binary)).to_be(true)
expect(async_proxy_tunnel_should_recv_client(over_client)).to_be(false)
expect(closed.closed).to_be(true)
expect(async_proxy_tunnel_should_recv_client(closed)).to_be(false)
expect(async_proxy_tunnel_should_recv_upstream(closed)).to_be(false)
```

</details>

#### should mark pending upstream connects timed out by budget

- Close proxy state that never completed upstream connect


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Close proxy state that never completed upstream connect")
val conn = async_proxy_connection_with_limits(
    10,
    "127.0.0.1:3000",
    "GET / HTTP/1.1\r\n\r\n",
    100,
    1024,
    4096,
    50,
    500
)
expect(async_proxy_connect_timed_out(conn, 120)).to_be(false)
expect(async_proxy_connect_timed_out(conn, 151)).to_be(true)
expect(async_proxy_timed_out(conn, 151)).to_be(true)
```

</details>

#### should mark idle established proxy streams timed out by budget

- Close proxy streams that stop making upstream or client progress


<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Close proxy streams that stop making upstream or client progress")
var conn = async_proxy_connection_with_limits(
    10,
    "127.0.0.1:3000",
    "GET / HTTP/1.1\r\n\r\n",
    100,
    1024,
    4096,
    50,
    500
)
conn.upstream_fd = 20
conn.last_activity_ms = 200
expect(async_proxy_idle_timed_out(conn, 650)).to_be(false)
expect(async_proxy_idle_timed_out(conn, 701)).to_be(true)
expect(async_proxy_timed_out(conn, 701)).to_be(true)
```

</details>

#### should summarize production hardening evidence for healthy proxy streams

- Report throughput and keep pressure flags clear for an active stream
- async proxy pool default config
   - Expected: evidence.reason equals `ok`
   - Expected: evidence.throughput_bytes_per_sec equals `2048`


<details>
<summary>Executable SSpec</summary>

Runnable source: 29 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Report throughput and keep pressure flags clear for an active stream")
var conn = async_proxy_connection_with_limits(
    10,
    "127.0.0.1:3000",
    "GET / HTTP/1.1\r\n\r\n",
    100,
    1024,
    4096,
    50,
    500
)
conn.upstream_fd = 20
conn.bytes_from_upstream = 2048
conn.last_activity_ms = 300
val stream = async_proxy_request_stream("POST / HTTP/1.1\r\n\r\n", 4, false, 8)
val evidence = async_proxy_connection_production_hardening(
    conn,
    stream,
    [],
    async_proxy_pool_default_config(),
    1100
)
expect(evidence.ok).to_be(true)
expect(evidence.reason).to_equal("ok")
expect(evidence.timed_out).to_be(false)
expect(evidence.request_backpressure).to_be(false)
expect(evidence.response_backpressure).to_be(false)
expect(evidence.pool_stressed).to_be(false)
expect(evidence.throughput_bytes_per_sec).to_equal(2048)
```

</details>

#### should prioritize timeout evidence over backpressure details

- Keep all flags visible while using timeout as the close reason
- var stream = async proxy request stream
- async proxy pool default config
   - Expected: evidence.reason equals `timeout`


<details>
<summary>Executable SSpec</summary>

Runnable source: 27 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Keep all flags visible while using timeout as the close reason")
var conn = async_proxy_connection_with_limits(
    10,
    "127.0.0.1:3000",
    "GET / HTTP/1.1\r\n\r\n",
    100,
    1024,
    4096,
    50,
    500
)
conn.pending_client_data = "abcdef"
conn.max_pending_client_bytes = 4
var stream = async_proxy_request_stream("POST / HTTP/1.1\r\n\r\n", 10, false, 4)
stream.pending_upstream_data = "abcdef"
val evidence = async_proxy_connection_production_hardening(
    conn,
    stream,
    [],
    async_proxy_pool_default_config(),
    151
)
expect(evidence.ok).to_be(false)
expect(evidence.reason).to_equal("timeout")
expect(evidence.timed_out).to_be(true)
expect(evidence.request_backpressure).to_be(true)
expect(evidence.response_backpressure).to_be(true)
```

</details>

#### should expose request backpressure as production hardening evidence

- Fail closed when upload buffering exceeds the configured pending upstream budget
- var stream = async proxy request stream
- async proxy pool default config
   - Expected: evidence.reason equals `request-backpressure`


<details>
<summary>Executable SSpec</summary>

Runnable source: 24 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Fail closed when upload buffering exceeds the configured pending upstream budget")
var conn = async_proxy_connection_with_limits(
    10,
    "127.0.0.1:3000",
    "POST / HTTP/1.1\r\n\r\n",
    100,
    1024,
    4096,
    50,
    500
)
conn.upstream_fd = 20
var stream = async_proxy_request_stream("POST / HTTP/1.1\r\n\r\n", 10, false, 4)
stream.pending_upstream_data = "abcdef"
val evidence = async_proxy_connection_production_hardening(
    conn,
    stream,
    [],
    async_proxy_pool_default_config(),
    120
)
expect(evidence.ok).to_be(false)
expect(evidence.reason).to_equal("request-backpressure")
expect(evidence.request_backpressure).to_be(true)
```

</details>

#### should expose downstream response backpressure as production hardening evidence

- Fail closed when pending client data exceeds the downstream send budget
- async proxy pool default config
   - Expected: evidence.reason equals `response-backpressure`


<details>
<summary>Executable SSpec</summary>

Runnable source: 25 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Fail closed when pending client data exceeds the downstream send budget")
var conn = async_proxy_connection_with_limits(
    10,
    "127.0.0.1:3000",
    "GET / HTTP/1.1\r\n\r\n",
    100,
    1024,
    4096,
    50,
    500
)
conn.upstream_fd = 20
conn.pending_client_data = "abcdef"
conn.max_pending_client_bytes = 4
val stream = async_proxy_request_stream("POST / HTTP/1.1\r\n\r\n", 4, false, 8)
val evidence = async_proxy_connection_production_hardening(
    conn,
    stream,
    [],
    async_proxy_pool_default_config(),
    120
)
expect(evidence.ok).to_be(false)
expect(evidence.reason).to_equal("response-backpressure")
expect(evidence.response_backpressure).to_be(true)
```

</details>

#### should expose full upstream pools as production hardening evidence

- Report pool pressure without failing an otherwise healthy request
   - Expected: evidence.reason equals `pool-stress`


<details>
<summary>Executable SSpec</summary>

Runnable source: 20 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Report pool pressure without failing an otherwise healthy request")
var conn = async_proxy_connection_with_limits(
    10,
    "127.0.0.1:3000",
    "GET / HTTP/1.1\r\n\r\n",
    100,
    1024,
    4096,
    50,
    500
)
conn.upstream_fd = 20
val config = AsyncProxyPoolConfig(max_idle_per_upstream: 1, idle_timeout_ms: 1000, max_reuse_count: 100)
val entries = [async_proxy_pool_entry("127.0.0.1:3000", 30, 100)]
val stream = async_proxy_request_stream("POST / HTTP/1.1\r\n\r\n", 4, false, 8)
val evidence = async_proxy_connection_production_hardening(conn, stream, entries, config, 120)
expect(async_proxy_pool_stressed(entries, "127.0.0.1:3000", config, 120)).to_be(true)
expect(evidence.ok).to_be(true)
expect(evidence.reason).to_equal("pool-stress")
expect(evidence.pool_stressed).to_be(true)
```

</details>

#### should export production hardening evidence through http server package

- Let worker and report code consume the hardened policy boundary from std.http_server
- exported async proxy request stream
- async proxy pool default config
   - Expected: evidence.reason equals `ok`


<details>
<summary>Executable SSpec</summary>

Runnable source: 21 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Let worker and report code consume the hardened policy boundary from std.http_server")
var conn = async_proxy_connection_with_limits(
    10,
    "127.0.0.1:3000",
    "GET / HTTP/1.1\r\n\r\n",
    100,
    1024,
    4096,
    50,
    500
)
conn.upstream_fd = 20
val evidence = exported_async_proxy_connection_production_hardening(
    conn,
    exported_async_proxy_request_stream("POST / HTTP/1.1\r\n\r\n", 0, false, 8),
    [],
    async_proxy_pool_default_config(),
    120
)
expect(evidence.ok).to_be(true)
expect(evidence.reason).to_equal("ok")
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 101 |
| Active scenarios | 101 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


## Related Documentation

- **Requirements:** [doc/02_requirements/feature/gpu_web_db_offload.md](doc/02_requirements/feature/gpu_web_db_offload.md)
- **Plan:** [doc/03_plan/agent_tasks/gpu_web_db_offload_impl_status.md](doc/03_plan/agent_tasks/gpu_web_db_offload_impl_status.md)
- **Design:** [doc/05_design/gpu_web_db_offload.md](doc/05_design/gpu_web_db_offload.md)


</details>
