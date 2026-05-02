# FR-NET-0006 Design — RDMA Exoskeleton Transport

Configuration:

- `RdmaTransportConfig` is the opt-in gate.
- `rdma_is_enabled` requires explicit enablement and a nonzero protection domain.
- `rdma_net_backend_capabilities` maps that gate to `supports_rdma`.

Memory:

- `RdmaMemoryRegion` records registered address, length, owner, keys, and active state.
- `rdma_deregister_memory` ends the lifetime by clearing keys and `registered`.

Queues and completions:

- `RdmaQueuePair` models send/receive completion queues owned by a worker or exoskeleton.
- `rdma_poll_completion` returns `RdmaCompletion` records that an async worker loop can consume.

Benchmark:

- `RdmaBenchmarkReport` and `rdma_benchmark_line` compare portable TCP and RDMA on identical fixtures.
