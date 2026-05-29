# FR-NET-0004 System Test Plan — Packet I/O Backend Boundary

System spec: `test/system/net_packet_io_boundary_spec.spl`

Coverage:

- Portable sockets remain the default and report `supports_packet_io == false`.
- Non-packet accelerated backends do not report packet I/O.
- Explicit packet-ring backends report packet I/O support.
- RX/TX leases are owned by the application until completion returns them to the driver.
- Benchmark output compares portable packets/sec and latency with packet-I/O packets/sec and latency for the same fixture.
