# SStack State: net-acceleration-remaining

## User Request
> next task from the plan — net_acceleration_remaining (P0 TCP correctness + capabilities, P1 HTTP server capability reporting, P2 DMA/QEMU tests)

## Task Type
feature

## Refined Goal
> Implement network acceleration infrastructure: TCP socket state machine with CONNECTING/ESTABLISHED transitions, net backend capability tiers (portable/sendfile/zero-copy/packet-io/sriov/rdma), DMA buffer sharing model for RX/TX, HTTP server capability reporting, QEMU test timeout scaffolding, and verification specs.

## Acceptance Criteria
- [ ] AC-1: TCP socket state machine — TcpState with SYN_SENT/CONNECTING/ESTABLISHED/CLOSE_WAIT transitions, active-open stays CONNECTING until ESTABLISHED
- [ ] AC-2: Socket publication — passive-open accepted connections queued only after ESTABLISHED, socket table tracks state
- [ ] AC-3: Net backend capabilities — NetBackendCapabilities with portable/sendfile/zero-copy/packet-io/sriov/rdma capability tiers
- [ ] AC-4: IoDriver capability exposure — net_capabilities() exposes runtime backend capabilities to library users
- [ ] AC-5: Network DMA buffers — RX/TX buffers using shared DMA descriptor model (same as file/block/VirtIO-GPU)
- [ ] AC-6: SR-IOV capability gating — SR-IOV reporting gated on isolation-domain state, trusted vs isolated distinction
- [ ] AC-7: HTTP server capability reporting — backend capability output on startup, throughput tier selection
- [ ] AC-8: QEMU test timeout — timeout-safe test phases, exact phase identification on failure, clean QEMU termination
- [ ] AC-9: Benchmark fixture — HTTP server benchmark with capability output, latency/throughput baseline
- [ ] AC-10: Verification spec — 20 tests covering TCP states, capabilities, DMA, HTTP reporting, timeouts

## Phase Checklist
- [x] 1-dev (Developer Lead) — 2026-05-18
- [x] 2-4 — skipped (plan doc comprehensive)
- [x] 5-implement (Engineer) — 2026-05-18
- [x] 6-refactor (Tech Lead) — 2026-05-18
- [x] 7-verify (QA) — 2026-05-18
- [x] 8-ship (Release Mgr) — 2026-05-18

## Phase Outputs

### 1-dev
10 ACs across P0/P1/P2. Existing: netstack/, socket_compat.spl, net_backend.spl, http_server/, qemu_runner.spl.

### 5-implement
5 parallel Sonnet agents. 4 source + 1 test:
- src/os/services/netstack/tcp_state_machine.spl — TcpState + SocketEntry + AcceptQueue + SocketTable
- src/os/services/netstack/net_capabilities.spl — NetBackendCapabilities + IoDriverCapability + CapabilityReport + ThroughputTier
- src/os/services/netstack/net_dma.spl — NetDmaBuffer + NetDmaPool + SriovCapability + NetAccelReport
- src/os/services/netstack/net_test_scaffold.spl — HttpCapReport + QemuTestPhase + QemuTestRunner + BenchmarkResult
- test/unit/os/net_acceleration_spec.spl — 20 tests

### 7-verify
20/20 tests PASS.
