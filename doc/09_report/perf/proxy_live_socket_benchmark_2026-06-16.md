# Proxy Live Socket Benchmark Evidence

Loopback sockets are opened for an HTTP relay and an Upgrade tunnel relay.
Harness runtimes: python_reference_loopback and native_simple_cached_proxy_loopback.
The native Simple row is generated from native-built Simple backend/proxy binaries; Python remains the process orchestrator and measurement client.

| name | runtime | iterations | p50_us | p95_us | p99_us | bytes | upstream_reuse | upstream_connects | max_rss_kb | timeouts | errors |
|---|---|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|
| live_socket_proxy_http_cached_50 | python_reference_loopback | 50 | 255 | 297 | 337 | 3200 | 49 | 1 | 13568 | 0 | 0 |
| live_socket_proxy_tunnel_50 | python_reference_loopback | 50 | 444 | 548 | 842 | 4200 | 0 | 0 | 13568 | 0 | 0 |
| native_simple_cached_proxy_http_50 | native_simple_cached_proxy_loopback | 50 | 606 | 671 | 750 | 6250 | 49 | 1 | 13568 | 0 | 0 |
