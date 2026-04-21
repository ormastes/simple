# Network Acceleration Feature Requests

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

## Open Requests

### FR-NET-0001 - Add connect completion and nonblocking socket semantics

- **Filed-on:** 2026-04-21
- **Filed-by:** Codex net acceleration implementation follow-up
- **Target:** `src/os/services/netstack/` and `src/os/posix/socket_compat.spl`
- **Priority:** P0
- **Status:** Open
- **Requested-semantics:**
  `connect()` must not report a completed TCP connection until the 3-way
  handshake reaches `ESTABLISHED`. Blocking sockets should wait or sleep on a
  bounded completion path; nonblocking sockets should return an errno-style
  in-progress result and allow readiness polling.
- **Acceptance-criteria:**
  - [ ] POSIX `connect()` distinguishes queued SYN from completed handshake.
  - [ ] Nonblocking TCP connect returns a documented in-progress code.
  - [ ] Poll/readiness reports writable only after TCP reaches `ESTABLISHED`.
  - [ ] QEMU netstack system test covers success, refused/RST, and timeout.
- **Related-upfront:** none
- **Related-design-doc:** tbd
- **Related-issue:** none
- **Notes:** The 2026-04-21 slice fixed internal socket publication timing, but
  the IPC response still returns success after queuing SYN.

### FR-NET-0002 - Complete TCP data path wakeups and close/error semantics

- **Filed-on:** 2026-04-21
- **Filed-by:** Codex net acceleration implementation follow-up
- **Target:** `src/os/services/netstack/tcp_connection.spl`
- **Priority:** P0
- **Status:** Open
- **Requested-semantics:**
  Finish the pure Simple TCP data path so socket send/recv operations have
  observable readiness, bounded buffering, peer close handling, RST propagation,
  and retransmission/timeout errors suitable for HTTP workloads.
- **Acceptance-criteria:**
  - [ ] `recv` blocks or reports would-block when the receive buffer is empty.
  - [ ] `send` applies send-window and buffer-cap limits instead of unbounded
        queue growth.
  - [ ] FIN, RST, retransmission exhaustion, and TIME_WAIT expose documented
        socket errors.
  - [ ] Tests cover empty recv, partial recv, remote close, RST, and timeout.
- **Related-upfront:** none
- **Related-design-doc:** tbd
- **Related-issue:** none
- **Notes:** `TcpConnection` already owns buffers; this request promotes the
  behavior from internal state machine support to application-visible sockets.

### FR-NET-0003 - Route HTTP static files through capability-driven sendfile

- **Filed-on:** 2026-04-21
- **Filed-by:** Codex net acceleration implementation follow-up
- **Target:** `src/lib/nogc_async_mut/http_server/`
- **Priority:** P1
- **Status:** Open
- **Requested-semantics:**
  Use `IoDriver.net_capabilities()` to select the fastest safe static-file
  response path: `sendfile` or zero-copy where supported, async read plus send
  otherwise. The portable behavior must remain the default for QEMU and CI.
- **Acceptance-criteria:**
  - [ ] Worker startup records backend capability summary per worker.
  - [ ] `ConnectionAction.SendFile` uses `submit_sendfile` only when the driver
        reports `supports_sendfile`.
  - [ ] Fallback path stays functional on portable socket backends.
  - [ ] Specs cover sendfile-capable and portable capability decisions.
- **Related-upfront:** none
- **Related-design-doc:** tbd
- **Related-issue:** none
- **Notes:** The capability model is implemented; HTTP worker routing is still
  pending.

### FR-NET-0004 - Add packet I/O backend boundary for AF_XDP or DPDK

- **Filed-on:** 2026-04-21
- **Filed-by:** Codex net acceleration implementation follow-up
- **Target:** `src/lib/nogc_async_mut/io/` and runtime backend adapters
- **Priority:** P1
- **Status:** Open
- **Requested-semantics:**
  Define a packet I/O backend boundary that can drive RX/TX rings through
  AF_XDP or DPDK while preserving the portable socket backend. This should be
  capability-gated and excluded from default QEMU CI unless explicitly enabled.
- **Acceptance-criteria:**
  - [ ] Backend capability reports `supports_packet_io` only for explicit
        packet-ring backends.
  - [ ] RX/TX ring ownership and buffer lifetime are documented and tested.
  - [ ] Portable socket backend remains the default when packet I/O is absent.
  - [ ] Microbenchmarks compare portable async sockets vs packet I/O on a
        fixture workload.
- **Related-upfront:** none
- **Related-design-doc:** tbd
- **Related-issue:** none

### FR-NET-0005 - Add SR-IOV VF discovery and assignment hooks

- **Filed-on:** 2026-04-21
- **Filed-by:** Codex net acceleration implementation follow-up
- **Target:** SimpleOS PCI/device manager and network backend capability layer
- **Priority:** P2
- **Status:** Open
- **Requested-semantics:**
  Discover SR-IOV-capable NIC physical functions, expose virtual function
  capabilities to the network backend layer, and allow explicit VF assignment
  to a net service or exoskeleton worker.
- **Acceptance-criteria:**
  - [ ] PCI capability scan identifies SR-IOV physical functions.
  - [ ] VF enablement remains opt-in and fails closed without IOMMU support.
  - [ ] Net backend capability reports `supports_sriov` only after a VF is
        assigned and isolated.
  - [ ] Docs specify QEMU/no-hardware fallback behavior.
- **Related-upfront:** none
- **Related-design-doc:** tbd
- **Related-issue:** none

### FR-NET-0006 - Prototype RDMA/exoskeleton transport for web serving

- **Filed-on:** 2026-04-21
- **Filed-by:** Codex net acceleration implementation follow-up
- **Target:** async HTTP server, memory registration, and network backend layer
- **Priority:** P2
- **Status:** Open
- **Requested-semantics:**
  Add an opt-in RDMA transport experiment for controlled deployments where web
  responses can use registered memory, queue pairs, and completion queues
  outside the normal TCP socket path. The default Simple web server must remain
  TCP-compatible.
- **Acceptance-criteria:**
  - [ ] RDMA backend is configured explicitly and never selected implicitly.
  - [ ] Memory registration lifetime is represented in Simple-owned types.
  - [ ] Completion queue polling integrates with the async worker loop.
  - [ ] Benchmark report compares RDMA path with portable TCP on the same
        static and dynamic response fixtures.
- **Related-upfront:** none
- **Related-design-doc:** tbd
- **Related-issue:** none
- **Notes:** This is a research prototype until isolation, memory safety, and
  fallback behavior are proven.

### FR-NET-0007 - Add network performance and timeout verification harness

- **Filed-on:** 2026-04-21
- **Filed-by:** Codex net acceleration implementation follow-up
- **Target:** network tests, QEMU scenarios, and smoke scripts
- **Priority:** P1
- **Status:** Open
- **Requested-semantics:**
  Create bounded network performance checks that measure connection setup,
  request latency, throughput, RSS, and timeout behavior for the portable
  stack and each accelerated backend.
- **Acceptance-criteria:**
  - [ ] QEMU network tests fail with a clear timeout reason instead of hanging.
  - [ ] HTTP server benchmark reports p50/p95 latency and throughput.
  - [ ] Backend capability summary is included in benchmark output.
  - [ ] Long native link or probe phases have explicit timeout reporting.
- **Related-upfront:** none
- **Related-design-doc:** tbd
- **Related-issue:** none
- **Notes:** `check-mcp-native-smoke.shs` passed on 2026-04-21 but spent 464s
  in native link for the MCP binary; future perf checks should make long phases
  visible and bounded.

### FR-NET-0008 - Share DMA buffer ownership with storage and display drivers

- **Filed-on:** 2026-04-21
- **Filed-by:** Codex cross-driver acceleration follow-up
- **Target:** `src/os/userlib/device.spl`, network drivers, block drivers, and
  display/GPU drivers
- **Priority:** P1
- **Status:** Open
- **Requested-semantics:**
  Promote the existing `SharedDmaBuffer` shape into a common driver contract so
  network, file/block, and display drivers can exchange caller-owned DMA
  buffers without copying through ordinary heap memory. The contract must make
  CPU-visible address, device-visible address, length, cache policy, ownership,
  and release rules explicit.
- **Acceptance-criteria:**
  - [ ] One shared DMA descriptor type is used by net, storage, and display
        driver APIs.
  - [ ] Cache flush/invalidate requirements are documented per memory kind.
  - [ ] DMA buffers are released through one audited cleanup path on task exit.
  - [ ] Tests cover double-free rejection, wrong-size free rejection, and
        driver handoff without aliasing ordinary heap slices.
- **Related-upfront:** `doc/04_architecture/hardware_driver_safety_and_performance_2026-04-15.md`
- **Related-design-doc:** `doc/03_plan/agent_tasks/dma_file_vga_driver_remaining_2026-04-21.md`
- **Related-issue:** none
- **Notes:** This is a prerequisite for safe zero-copy network RX/TX, storage
  direct I/O, and VirtIO-GPU transfer buffers.

### FR-NET-0009 - Gate SR-IOV and DMA on IOMMU-capable isolation

- **Filed-on:** 2026-04-21
- **Filed-by:** Codex cross-driver acceleration follow-up
- **Target:** SimpleOS PCI/device grants, DMA syscalls, and net backend layer
- **Priority:** P1
- **Status:** Open
- **Requested-semantics:**
  SR-IOV virtual functions and high-throughput DMA paths must only be exposed to
  user-space or exoskeleton drivers when the device grant includes an isolation
  domain. No-IOMMU systems may use trusted early-boot drivers, but must not
  advertise SR-IOV or user-owned DMA acceleration as isolated.
- **Acceptance-criteria:**
  - [ ] Device grants include an isolation-domain field or explicit
        no-isolation marker.
  - [ ] SR-IOV VF assignment fails closed without IOMMU or equivalent
        isolation.
  - [ ] DMA allocation records the owning device/function and rejects reuse by
        unrelated drivers.
  - [ ] Network capability reporting distinguishes `sriov-available` from
        `sriov-isolated`.
- **Related-upfront:** `doc/04_architecture/hardware_driver_safety_and_performance_2026-04-15.md`
- **Related-design-doc:** `doc/03_plan/agent_tasks/dma_file_vga_driver_remaining_2026-04-21.md`
- **Related-issue:** none
