# FR-NET-0007 System Test Plan — Network Performance and Timeout Harness

System spec: `test/system/net_perf_timeout_harness_spec.spl`

Coverage:

- QEMU network timeout reports include the phase name and timeout limit.
- Long native link/probe timeout reports include elapsed time and limit.
- HTTP benchmark reports include backend summary, connection setup, p50, p95, throughput, and max RSS.
