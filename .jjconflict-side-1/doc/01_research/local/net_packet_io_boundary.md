# FR-NET-0004 Local Research — Packet I/O Backend Boundary

Status: implemented research note.

Existing code:

- `src/lib/nogc_async_mut/io/net_backend.spl` already models `supports_packet_io` and exposes `packet_io_net_backend_capabilities`.
- `src/lib/nogc_async_mut/io/packet_io.spl` already models disabled and opt-in packet-ring capabilities plus RX/TX buffer leases.
- `test/unit/lib/nogc_async_mut/io/net_backend_spec.spl` already covered default disabled behavior and lease completion.

Missing pieces were a stable benchmark comparison artifact, system-level traceability, and tracker/design docs. The implementation adds a small pure `PacketIoBenchmarkReport` so CI or runtime harnesses can compare portable sockets and packet I/O on the same fixture without enabling AF_XDP/DPDK in default tests.
