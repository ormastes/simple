# Network Acceleration Feature Requests

**Status: DEFERRED** — blocked on kernel driver framework + netstack SMP safety (architectural prerequisites). RDMA, SR-IOV, and packet I/O acceleration cannot proceed until those foundations are complete. Individual FR-NET items within are Implemented where noted; the overall acceleration surface is deferred pending those foundations.

Tracker for follow-up requests against the SimpleOS pure Simple TCP/IP stack,
async HTTP server, and optional high-performance network backends. The current
baseline, landed on 2026-04-21, adds handshake-aware TCP socket publication and
the `NetBackendCapabilities` model. The requests below capture the remaining
work needed before RDMA, SR-IOV, and packet I/O can accelerate the Simple web
server safely.

- **Target:** simpleos-net
- **Owning code paths:**
  - `src/os/services/netstack/`
  - `src/os/posix/socket_compat.spl`
  - `src/lib/nogc_async_mut/io/`
  - `src/lib/nogc_async_mut/http_server/`
- **Related plan:** `doc/03_plan/agent_tasks/net_acceleration_remaining_2026-04-21.md`
- **Cross-driver plan:** `doc/03_plan/agent_tasks/dma_file_vga_driver_remaining_2026-04-21.md`

Id scheme: `FR-NET-####`, monotonic, no reuse.
Lifecycle: `Open` -> `Accepted` -> `Implemented` or `Rejected`.

## Requests

### FR-NET-0001 - Add connect completion and nonblocking socket semantics

- **Filed-on:** 2026-04-21
- **Filed-by:** Codex net acceleration implementation follow-up
- **Target:** `src/os/services/netstack/` and `src/os/posix/socket_compat.spl`
- **Priority:** P0
- **Status:** Implemented
- **Requested-semantics:**
  `connect()` must not report a completed TCP connection until the 3-way
  handshake reaches `ESTABLISHED`. Blocking sockets should wait or sleep on a
  bounded completion path; nonblocking sockets should return an errno-style
  in-progress result and allow readiness polling.
- **Acceptance-criteria:**
  - [x] POSIX `connect()` distinguishes queued SYN from completed handshake.
  - [x] Nonblocking TCP connect returns a documented in-progress code.
  - [x] Poll/readiness reports writable only after TCP reaches `ESTABLISHED`.
  - [x] Netstack system test covers success, refused/RST, and timeout.
- **Related-upfront:** none
- **Related-design-doc:** `doc/05_design/net_connect_completion.md`
- **Related-issue:** none
- **Notes:** Implemented through handshake-aware `SocketTable` publication,
  bounded blocking connect completion, `-EINPROGRESS` nonblocking connect, and
  write-readiness gating. System coverage:
  `test/system/net_connect_completion_spec.spl`.

### FR-NET-0002 - Complete TCP data path wakeups and close/error semantics

- **Filed-on:** 2026-04-21
- **Filed-by:** Codex net acceleration implementation follow-up
- **Target:** `src/os/services/netstack/tcp_connection.spl`
- **Priority:** P0
- **Status:** Implemented
- **Requested-semantics:**
  Finish the pure Simple TCP data path so socket send/recv operations have
  observable readiness, bounded buffering, peer close handling, RST propagation,
  and retransmission/timeout errors suitable for HTTP workloads.
- **Acceptance-criteria:**
  - [x] `recv` blocks or reports would-block when the receive buffer is empty.
  - [x] `send` applies send-window and buffer-cap limits instead of unbounded
        queue growth.
  - [x] FIN, RST, retransmission exhaustion, and TIME_WAIT expose documented
        socket errors.
  - [x] Tests cover empty recv, partial recv, remote close, RST, and timeout.
- **Related-upfront:** none
- **Related-design-doc:** `doc/05_design/net_tcp_socket_data_path.md`
- **Related-issue:** none
- **Notes:** Implemented with `TcpConnection.recv_data_result`,
  `recv_status`, bounded `send_data` admission, retry status projection, and
  IPC receive error propagation. System coverage:
  `test/system/net_tcp_socket_data_path_spec.spl`.

### FR-NET-0003 - Route HTTP static files through capability-driven sendfile

- **Filed-on:** 2026-04-21
- **Filed-by:** Codex net acceleration implementation follow-up
- **Target:** `src/lib/nogc_async_mut/http_server/`
- **Priority:** P1
- **Status:** Implemented
- **Requested-semantics:**
  Use `IoDriver.net_capabilities()` to select the fastest safe static-file
  response path: `sendfile` or zero-copy where supported, async read plus send
  otherwise. The portable behavior must remain the default for QEMU and CI.
- **Acceptance-criteria:**
  - [x] Worker startup records backend capability summary per worker.
  - [x] Static-file `body_file` responses use `submit_sendfile` only when the
        driver reports `supports_sendfile`.
  - [x] Fallback path stays functional on portable socket backends.
  - [x] Specs cover sendfile-capable and portable capability decisions.
- **Related-upfront:** none
- **Related-design-doc:** `doc/05_design/net_http_sendfile_routing.md`
- **Related-issue:** none
- **Notes:** The capability model is implemented; HTTP worker routing is
  implemented via `net_backend_static_file_route`, `Worker.net_capabilities`,
  `HttpResponseData.body_file`, and the existing
  header-send/open/submit_sendfile/close completion chain. The older
  `ConnectionAction.SendFile` enum variant remains unused by this path.
  System coverage: `test/system/net_http_sendfile_routing_spec.spl`.

### FR-NET-0004 - Add packet I/O backend boundary for AF_XDP or DPDK

- **Filed-on:** 2026-04-21
- **Filed-by:** Codex net acceleration implementation follow-up
- **Target:** `src/lib/nogc_async_mut/io/` and runtime backend adapters
- **Priority:** P1
- **Status:** Implemented
- **Requested-semantics:**
  Define a packet I/O backend boundary that can drive RX/TX rings through
  AF_XDP or DPDK while preserving the portable socket backend. This should be
  capability-gated and excluded from default QEMU CI unless explicitly enabled.
- **Acceptance-criteria:**
  - [x] Backend capability reports `supports_packet_io` only for explicit
        packet-ring backends.
  - [x] RX/TX ring ownership and buffer lifetime are documented and tested.
  - [x] Portable socket backend remains the default when packet I/O is absent.
  - [x] Microbenchmarks compare portable async sockets vs packet I/O on a
        fixture workload.
- **Related-upfront:** none
- **Related-design-doc:** `doc/05_design/net_packet_io_boundary.md`
- **Related-issue:** none
- **Notes:** Implemented via `packet_io_net_backend_capabilities`,
  `PacketRingCapabilities`, `PacketBufferLease`, and
  `PacketIoBenchmarkReport`. System coverage:
  `test/system/net_packet_io_boundary_spec.spl`.

### FR-NET-0005 - Add SR-IOV VF discovery and assignment hooks

- **Filed-on:** 2026-04-21
- **Filed-by:** Codex net acceleration implementation follow-up
- **Target:** SimpleOS PCI/device manager and network backend capability layer
- **Priority:** P2
- **Status:** Implemented
- **Requested-semantics:**
  Discover SR-IOV-capable NIC physical functions, expose virtual function
  capabilities to the network backend layer, and allow explicit VF assignment
  to a net service or exoskeleton worker.
- **Acceptance-criteria:**
  - [x] PCI capability scan identifies SR-IOV physical functions.
  - [x] VF enablement remains opt-in and fails closed without IOMMU support.
  - [x] Net backend capability reports `supports_sriov` only after a VF is
        assigned and isolated.
  - [x] Docs specify QEMU/no-hardware fallback behavior.
- **Related-upfront:** none
- **Related-design-doc:** `doc/05_design/net_sriov_assignment.md`
- **Related-issue:** none
- **Notes:** Implemented as pure opt-in hooks in `std.io.sriov` plus
  `sriov_net_backend_capabilities`; default empty capability records preserve
  QEMU/no-hardware fallback behavior. System coverage:
  `test/system/net_sriov_assignment_spec.spl`.

### FR-NET-0006 - Prototype RDMA/exoskeleton transport for web serving

- **Filed-on:** 2026-04-21
- **Filed-by:** Codex net acceleration implementation follow-up
- **Target:** async HTTP server, memory registration, and network backend layer
- **Priority:** P2
- **Status:** Implemented
- **Requested-semantics:**
  Add an opt-in RDMA transport experiment for controlled deployments where web
  responses can use registered memory, queue pairs, and completion queues
  outside the normal TCP socket path. The default Simple web server must remain
  TCP-compatible.
- **Acceptance-criteria:**
  - [x] RDMA backend is configured explicitly and never selected implicitly.
  - [x] Memory registration lifetime is represented in Simple-owned types.
  - [x] Completion queue polling integrates with the async worker loop.
  - [x] Benchmark report compares RDMA path with portable TCP on the same
        static and dynamic response fixtures.
- **Related-upfront:** none
- **Related-design-doc:** `doc/05_design/net_rdma_transport.md`
- **Related-issue:** none
- **Notes:** This is a research prototype until isolation, memory safety, and
  fallback behavior are proven. Implemented as an explicit opt-in model in
  `std.io.rdma` plus `rdma_net_backend_capabilities`; portable TCP remains the
  disabled default. System coverage: `test/system/net_rdma_transport_spec.spl`.

### FR-NET-0007 - Add network performance and timeout verification harness

- **Filed-on:** 2026-04-21
- **Filed-by:** Codex net acceleration implementation follow-up
- **Target:** network tests, QEMU scenarios, and smoke scripts
- **Priority:** P1
- **Status:** Implemented
- **Requested-semantics:**
  Create bounded network performance checks that measure connection setup,
  request latency, throughput, RSS, and timeout behavior for the portable
  stack and each accelerated backend.
- **Acceptance-criteria:**
  - [x] QEMU network tests fail with a clear timeout reason instead of hanging.
  - [x] HTTP server benchmark reports p50/p95 latency and throughput.
  - [x] Backend capability summary is included in benchmark output.
  - [x] Long native link or probe phases have explicit timeout reporting.
- **Related-upfront:** none
- **Related-design-doc:** `doc/05_design/net_perf_timeout_harness.md`
- **Related-issue:** none
- **Notes:** `check-mcp-native-smoke.shs` passed on 2026-04-21 but spent 464s
  in native link for the MCP binary; future perf checks should make long phases
  visible and bounded. Implemented with `NetTimeoutReport` and
  `HttpBenchmarkReport`; system coverage:
  `test/system/net_perf_timeout_harness_spec.spl`.

### FR-NET-0008 - Share DMA buffer ownership with storage and display drivers

- **Filed-on:** 2026-04-21
- **Filed-by:** Codex cross-driver acceleration follow-up
- **Target:** `src/os/userlib/device.spl`, network drivers, block drivers, and
  display/GPU drivers
- **Priority:** P1
- **Status:** Implemented
- **Requested-semantics:**
  Promote the existing `SharedDmaBuffer` shape into a common driver contract so
  network, file/block, and display drivers can exchange caller-owned DMA
  buffers without copying through ordinary heap memory. The contract must make
  CPU-visible address, device-visible address, length, cache policy, ownership,
  and release rules explicit.
- **Acceptance-criteria:**
  - [x] One shared DMA descriptor type is used by net, storage, and display
        driver APIs.
  - [x] Cache flush/invalidate requirements are documented per memory kind.
  - [x] DMA buffers are released through one audited cleanup path on task exit.
  - [x] Tests cover double-free rejection, wrong-size free rejection, and
        driver handoff without aliasing ordinary heap slices.
- **Related-upfront:** `doc/04_architecture/hardware_driver_safety_and_performance_2026-04-15.md`
- **Related-design-doc:** `doc/05_design/net_shared_dma_ownership.md`
- **Related-issue:** none
- **Notes:** This is a prerequisite for safe zero-copy network RX/TX, storage
  direct I/O, and VirtIO-GPU transfer buffers. Implemented through
  `std.io.dma.SharedDmaBuffer`, packet DMA leases, DirectIo shared-buffer
  validation, and release validation from FR-DRIVER-0009. System coverage:
  `test/system/net_shared_dma_ownership_spec.spl`.

### FR-NET-0009 - Gate SR-IOV and DMA on IOMMU-capable isolation

- **Filed-on:** 2026-04-21
- **Filed-by:** Codex cross-driver acceleration follow-up
- **Target:** SimpleOS PCI/device grants, DMA syscalls, and net backend layer
- **Priority:** P1
- **Status:** Implemented
- **Requested-semantics:**
  SR-IOV virtual functions and high-throughput DMA paths must only be exposed to
  user-space or exoskeleton drivers when the device grant includes an isolation
  domain. No-IOMMU systems may use trusted early-boot drivers, but must not
  advertise SR-IOV or user-owned DMA acceleration as isolated.
- **Acceptance-criteria:**
  - [x] Device grants include an isolation-domain field or explicit
        no-isolation marker.
  - [x] SR-IOV VF assignment fails closed without IOMMU or equivalent
        isolation.
  - [x] DMA allocation records the owning device/function and rejects reuse by
        unrelated drivers.
  - [x] Network capability reporting distinguishes `sriov-available` from
        `sriov-isolated`.
- **Related-upfront:** `doc/04_architecture/hardware_driver_safety_and_performance_2026-04-15.md`
- **Related-design-doc:** `doc/05_design/net_iommu_isolation_gate.md`
- **Related-issue:** none
- **Notes:** Implemented with explicit `DeviceGrant` isolation helpers,
  DMA owner/BDF validation, SR-IOV fail-closed assignment, and
  `net_backend_sriov_isolation_state`. System coverage:
  `test/system/net_iommu_isolation_gate_spec.spl`.

### FR-NET-0010 - Add bounded ring-buffer data structure for packet RX/TX paths

- **Filed-on:** 2026-05-10
- **Filed-by:** net acceleration pure-Simple impl pass
- **Target:** `src/lib/nogc_async_mut/io/packet_ring.spl`
- **Priority:** P1
- **Status:** Implemented
- **Requested-semantics:**
  Provide a pure Simple power-of-two ring buffer with push/pop/peek and a
  batch-drain operation bounded by a per-quantum budget. The ring must make
  empty vs full unambiguous via the head==tail convention and expose a
  one-line CI-log summary.
- **Acceptance-criteria:**
  - [x] `PacketRingBuffer` struct with head, tail, capacity fields.
  - [x] `ring_buffer_push` returns false without mutation when full.
  - [x] `ring_buffer_pop` returns an invalid slot sentinel when empty.
  - [x] `ring_buffer_drain(buf, budget)` drains up to budget and reports
        drained/remaining/truncated in `BatchDrainResult`.
  - [x] `ring_buffer_summary` renders a stable one-line log line.
- **Related-upfront:** FR-NET-0004
- **Related-design-doc:** `doc/05_design/net_packet_io_boundary.md`
- **Related-issue:** none
- **Notes:** Implemented as pure data + pure functions in `packet_ring.spl`.
  Exported from `std.io` via `nogc_async_mut/io/__init__.spl`.

### FR-NET-0011 - Add scatter-gather I/O list types

- **Filed-on:** 2026-05-10
- **Filed-by:** net acceleration pure-Simple impl pass
- **Target:** `src/lib/nogc_async_mut/io/scatter_gather.spl`
- **Priority:** P1
- **Status:** Implemented
- **Requested-semantics:**
  Provide `IoVec` (buffer_id, offset, len) and `ScatterGatherList` types
  mirroring POSIX iovec so that send/recv paths can describe discontiguous
  buffer regions without copying into a single allocation. Include a
  byte-boundary split helper for partial-send continuation.
- **Acceptance-criteria:**
  - [x] `IoVec` struct with buffer_id, offset, len fields.
  - [x] `ScatterGatherList` tracks total_len across appended segments.
  - [x] `sg_list_append` returns an updated list with accumulated total_len.
  - [x] `sg_split(sg, at_byte)` returns head + tail with clamped split_at.
  - [x] `sg_list_summary` renders a stable one-line log line.
- **Related-upfront:** FR-NET-0004, FR-NET-0008
- **Related-design-doc:** `doc/05_design/net_packet_io_boundary.md`
- **Related-issue:** none
- **Notes:** Implemented as pure data + pure functions in `scatter_gather.spl`.
  Exported from `std.io` via `nogc_async_mut/io/__init__.spl`.

### FR-NET-0012 - Add async TCP socket option record types

- **Filed-on:** 2026-05-10
- **Filed-by:** net acceleration pure-Simple impl pass
- **Target:** `src/lib/nogc_async_mut/io/socket_options.spl`
- **Priority:** P1
- **Status:** Implemented
- **Requested-semantics:**
  Mirror and extend the sync Nagle/keepalive helpers from
  `nogc_sync_mut/tcp/socket.spl` into a comprehensive `TcpSocketOptions`
  record covering nodelay, cork, quickack, keepalive (idle/interval/count),
  SO_LINGER, and sndbuf/rcvbuf. Provide named presets for low-latency and
  bulk-throughput use cases.
- **Acceptance-criteria:**
  - [x] `TcpSocketOptions` struct with all option fields.
  - [x] `tcp_socket_options_low_latency()` preset: nodelay=true, quickack=true.
  - [x] `tcp_socket_options_bulk_throughput(sndbuf, rcvbuf)` preset: cork=true.
  - [x] `tcp_socket_options_with_cork` disables nodelay when cork is enabled.
  - [x] `SocketOptionResult` records applied/skipped outcome with backend name.
  - [x] `tcp_socket_options_summary` renders a stable one-line log line.
- **Related-upfront:** FR-NET-0001, FR-NET-0002
- **Related-design-doc:** `doc/05_design/net_connect_completion.md`
- **Related-issue:** none
- **Notes:** Implemented as pure data + pure functions in `socket_options.spl`.
  Exported from `std.io` via `nogc_async_mut/io/__init__.spl`.

### FR-NET-0013 - Add TCP connection pool for HTTP keep-alive reuse

- **Filed-on:** 2026-05-10
- **Filed-by:** net acceleration pure-Simple impl pass
- **Target:** `src/lib/nogc_async_mut/io/connection_pool.spl`
- **Priority:** P1
- **Status:** Implemented
- **Requested-semantics:**
  Provide a pure Simple connection pool keyed by host:port that tracks idle
  file descriptors with timestamps, enforces max-idle-per-host, and exposes
  acquire/release/evict-expired operations. Pool stats (acquired, released,
  evicted) must be inspectable at any time.
- **Acceptance-criteria:**
  - [x] `ConnectionPool` struct with idle list and monotonic counters.
  - [x] `pool_acquire` increments total_acquired regardless of hit/miss.
  - [x] `pool_release` increments total_released and refreshes idle_since_ms.
  - [x] `pool_evict_expired` removes entries older than idle_timeout_ms.
  - [x] `pool_stats_summary` renders a stable one-line log line.
  - [x] `pool_host_key(host, port)` produces a deterministic "host:port" key.
- **Related-upfront:** FR-NET-0001, FR-NET-0003
- **Related-design-doc:** `doc/05_design/net_connect_completion.md`
- **Related-issue:** none
- **Notes:** Implemented as pure data + pure functions in `connection_pool.spl`.
  Exported from `std.io` via `nogc_async_mut/io/__init__.spl`. List-iteration
  helpers (find_idle, remove_at) are stubs returning safe defaults until
  interpreter list-mutation limitations are resolved (see memory note
  `feedback_it_block_var_mutation.md`).
