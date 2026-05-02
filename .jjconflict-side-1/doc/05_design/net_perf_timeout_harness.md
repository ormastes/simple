# FR-NET-0007 Design — Network Performance and Timeout Harness

Timeout reporting:

- `NetTimeoutReport` is populated by QEMU, native-link, or probe phases.
- `net_timeout_report` marks a timeout when elapsed time reaches or exceeds a nonzero timeout budget.
- Messages include phase, elapsed time, and limit so failures do not look like hangs.

Benchmark reporting:

- `HttpBenchmarkReport` is the shared HTTP server benchmark shape.
- It records backend summary, connection setup latency, p50/p95 request latency, throughput, and max RSS.
- `http_benchmark_line` renders a stable one-line CI/log artifact.
