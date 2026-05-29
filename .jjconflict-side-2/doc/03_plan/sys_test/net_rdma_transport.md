# FR-NET-0006 System Test Plan — RDMA Exoskeleton Transport

System spec: `test/system/net_rdma_transport_spec.spl`

Coverage:

- RDMA remains disabled by default.
- RDMA backend capability is reported only for explicit nonzero protection-domain config.
- Memory registration and deregistration lifetime is represented in Simple-owned types.
- Queue-pair completion polling produces worker-consumable completion records.
- Benchmark output compares portable TCP and RDMA on the same fixture.
