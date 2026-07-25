# FR-NET-0007 Local Research — Network Performance and Timeout Harness

Status: implemented research note.

Existing state:

- QEMU runner paths already use `rt_process_run_timeout` and print timeout/elapsed values in several build/test lanes.
- Net acceleration backend models now provide stable backend summaries.
- Packet-I/O and RDMA slices added per-backend benchmark report records, but no common HTTP benchmark/timeout report existed.

Implementation:

- `std.io.net_perf.NetTimeoutReport` records phase, elapsed time, timeout, and a clear message.
- `std.io.net_perf.HttpBenchmarkReport` records connection setup, p50/p95 latency, throughput, RSS, and backend summary.
- The system spec keeps the reporting contract stable without launching QEMU in default CI.
