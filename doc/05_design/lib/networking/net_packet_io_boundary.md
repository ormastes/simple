# FR-NET-0004 Design — Packet I/O Backend Boundary

Capability boundary:

- Portable socket backends use `portable_net_backend_capabilities` and never report packet I/O.
- Explicit packet-ring backends use `packet_io_net_backend_capabilities`.
- `PacketRingCapabilities` records RX entries, TX entries, and whether the configured backend is zero-copy.

Ownership:

- `PacketBufferLease` carries ring id, buffer id, direction, owner, length, and completion state.
- RX and TX lease constructors hand ownership to the application.
- `packet_complete` returns ownership to the driver completion queue.

Benchmark artifact:

- `PacketIoBenchmarkReport` stores one fixture's portable and packet-I/O throughput/latency.
- `packet_io_benchmark_line` renders a stable one-line summary for CI logs and benchmark reports.
