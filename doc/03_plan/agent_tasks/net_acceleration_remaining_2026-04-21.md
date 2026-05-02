# Net Acceleration Remaining Plan

Status: open
Last updated: 2026-04-21
Scope: pure Simple TCP/IP stack, POSIX socket compatibility, async HTTP server,
and optional high-performance backends for packet I/O, SR-IOV, and RDMA.

Related:
- `doc/08_tracking/feature_request/net_acceleration_requests.md`
- `doc/03_plan/agent_tasks/dma_file_vga_driver_remaining_2026-04-21.md`
- `src/os/services/netstack/`
- `src/os/posix/socket_compat.spl`
- `src/lib/nogc_async_mut/io/net_backend.spl`
- `src/lib/nogc_async_mut/http_server/`

## Current Baseline

Completed in the 2026-04-21 implementation slice:

- TCP active-open sockets stay `CONNECTING` internally until the TCP state
  machine reaches `ESTABLISHED`.
- Passive-open accepted connections are queued only after the final ACK moves
  the connection to `ESTABLISHED`.
- Socket table direct send/recv no longer pretends to own TCP payload buffers.
- `NetBackendCapabilities` models portable, sendfile, zero-copy, packet I/O,
  SR-IOV, and RDMA capability tiers.
- `IoDriver.net_capabilities()` exposes the runtime async backend to library
  users.
- Focused specs cover TCP socket publication and backend capability decisions.

## Remaining Work Order

### P0 - Correct socket-visible TCP behavior

1. Finish connect completion semantics.
   - Feature request: `FR-NET-0001`
   - Files:
     - `src/os/services/netstack/netstack_service.spl`
     - `src/os/posix/socket_compat.spl`
     - `src/os/userlib/net.spl`
   - Acceptance:
     - Blocking `connect` waits for completed handshake or returns timeout,
       refused, or unreachable.
     - Nonblocking `connect` returns a documented in-progress code.
     - Poll/readiness transitions to writable after `ESTABLISHED`.
     - QEMU network test covers success and timeout/refused paths.

2. Complete TCP data path socket behavior.
   - Feature request: `FR-NET-0002`
   - Files:
     - `src/os/services/netstack/tcp_connection.spl`
     - `src/os/services/netstack/netstack_service.spl`
     - `src/os/services/netstack/socket.spl`
   - Acceptance:
     - Empty receive has blocking or would-block behavior.
     - Send buffers have explicit caps and window-aware queuing.
     - FIN, RST, retransmission exhaustion, and TIME_WAIT surface to sockets.
     - Tests cover partial reads, peer close, RST, and timeout.

3. Add timeout-safe QEMU net tests.
   - Feature request: `FR-NET-0007`
   - Files:
     - `test/system/os_network_spec.spl`
     - `src/os/qemu_runner.spl`
     - nearest QEMU scenario config
   - Acceptance:
     - Test failure prints the exact phase that timed out.
     - Timeout exit path terminates QEMU without orphaning the test process.
     - Serial output includes socket fd, state, and backend capability summary.

### P1 - Connect async web server to backend capabilities

1. Route static-file responses through capability gates.
   - Feature request: `FR-NET-0003`
   - Files:
     - `src/lib/nogc_async_mut/http_server/worker.spl`
     - `src/lib/nogc_async_mut/http_server/connection.spl`
     - `src/lib/nogc_async_mut/http_server/static_file.spl`
   - Acceptance:
     - `ConnectionAction.SendFile` uses `IoDriver.submit_sendfile` only when
       `supports_sendfile` is true.
     - Portable fallback uses async read plus send.
     - Specs pin both capability paths.

2. Add capability reporting to HTTP server startup.
   - Feature request: `FR-NET-0003`
   - Files:
     - `src/lib/nogc_async_mut/http_server/server.spl`
     - `src/lib/nogc_async_mut/http_server/worker.spl`
   - Acceptance:
     - Each worker records backend name and acceleration tier.
     - Access or diagnostic output can include `portable`, `sendfile`,
       `zero-copy`, `sriov-packet`, or `rdma`.
     - No runtime FFI is required for portable tests.

3. Add portable performance fixtures.
   - Feature request: `FR-NET-0007`
   - Files:
     - `test/perf/`
     - `test/perf/bench/` or existing benchmark runner
   - Acceptance:
     - Reports connection setup latency, p50/p95 request latency, throughput,
       and RSS.
     - Benchmark output includes backend capability summary.

### P1 - Packet I/O backend boundary

1. Define packet ring ownership API.
   - Feature request: `FR-NET-0004`
   - Files:
     - `src/lib/nogc_async_mut/io/`
     - runtime backend headers if a C boundary is needed
   - Acceptance:
     - RX/TX buffer ownership is explicit and testable.
     - Portable socket backend remains independent from packet-ring code.
     - Backend reports `supports_packet_io` only when explicitly configured.

2. Prototype AF_XDP or DPDK adapter behind the boundary.
   - Feature request: `FR-NET-0004`
   - Acceptance:
     - Adapter can be compiled out on unsupported hosts.
     - CI defaults to portable backend.
     - Microbenchmark compares portable async sockets to packet I/O on the
       same request fixture.

### P2 - Hardware acceleration experiments

1. Add SR-IOV discovery and assignment hooks.
   - Feature request: `FR-NET-0005`
   - Acceptance:
     - PCI scan identifies SR-IOV physical functions.
     - VF enablement is opt-in and requires isolation support.
     - Capability layer reports `supports_sriov` only for assigned VFs.

2. Share DMA ownership with storage and display drivers.
   - Feature requests: `FR-NET-0008`, `FR-NET-0009`
   - Cross-driver plan:
     `doc/03_plan/agent_tasks/dma_file_vga_driver_remaining_2026-04-21.md`
   - Acceptance:
     - Network RX/TX buffers use the same shared DMA descriptor model as
       file/block direct I/O and VirtIO-GPU transfer buffers.
     - SR-IOV capability reporting is gated on isolation-domain state.
     - No-IOMMU trusted-driver mode is clearly distinguished from isolated
       acceleration.

3. Prototype RDMA/exoskeleton web transport.
   - Feature request: `FR-NET-0006`
   - Acceptance:
     - RDMA is explicit configuration only.
     - Registered memory lifetime is represented by Simple-owned types.
     - Completion queues integrate with async worker polling.
     - Benchmark compares RDMA with portable TCP on identical fixtures.

## Verification Gates

Every implementation wave must run:

- Focused unit specs for touched modules.
- `git diff --check`.
- Stub scan on touched files: `TODO`, `pass_todo`, `stub`, `placeholder`,
  `not implemented`, and `expect(true).to_equal(true)`.
- `sh scripts/check-core-runtime-smoke.shs bin/simple` after `src/lib` changes.
- `SIMPLE_BINARY=bin/simple sh scripts/check-mcp-native-smoke.shs` after
  compiler/core/lib changes that can affect MCP/LSP startup.

Network implementation waves should also add or update:

- QEMU network scenario with bounded timeout.
- HTTP server benchmark fixture with backend capability output.
- Regression spec for each socket-visible TCP state transition.

## Do Not Start Yet

- Do not make RDMA or SR-IOV default paths.
- Do not select packet I/O automatically based on host presence.
- Do not bypass the pure Simple TCP/socket behavior fixes with a host-only
  shortcut.
- Do not treat throughput wins as valid unless latency, RSS, timeout, and
  fallback behavior are measured on the same fixture.
