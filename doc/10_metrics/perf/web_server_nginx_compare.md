# Web Server NGINX Comparison Metrics

## Benchmark Normalization

| payload_policy | keepalive_policy | connections | threads | duration_seconds | worker_policy | logging_policy | cpu_affinity_policy |
|---|---|---:|---:|---:|---|---|---|
| same bytes per compared workload | wrk default keep-alive | 1 | 1 | 1 | one measured server worker unless wrapper overrides both sides | access logging disabled for measured hot path | not pinned on this host; report must say so |

| workload | simple_target | external_baseline | load_tool | status | simple_rps | external_rps | rps_ratio | simple_p99_ms | external_p99_ms | throughput_mbps | failures | reason |
|---|---|---|---|---|---:|---:|---:|---:|---:|---:|---:|---|
| static_1kb | native_simple_static_1024 | nginx_static_1024 | wrk | measured | 2551.83 | 15460.12 | 0.165 | 0.449 | 0.090 | 126.649 | 0 | live-simple-nginx-wrk |
| static_1kb | native_simple_static_1024 | caddy_static_1024 | wrk | measured | 2351.70 | 3776.07 | 0.623 | 0.499 | 0.409 | 30.934 | 0 | live-simple-caddy-wrk |
| static_1kb | native_simple_static_1024 | h2o_static_1024 | wrk | measured | 2281.64 | 9389.05 | 0.243 | 0.523 | 0.123 | 76.915 | 0 | live-simple-h2o-wrk |
| static_1mb | native_simple_static_1048576 | nginx_static_1048576 | wrk | measured | 835.83 | 1380.71 | 0.605 | 1.600 | 1.170 | 11582.235 | 0 | live-simple-nginx-wrk |
| static_1mb | native_simple_static_1048576 | caddy_static_1048576 | wrk | measured | 267.30 | 1359.38 | 0.197 | 4.800 | 0.930 | 11403.306 | 0 | live-simple-caddy-wrk |
| static_1mb | native_simple_static_1048576 | h2o_static_1048576 | wrk | measured | 261.93 | 1201.20 | 0.218 | 4.780 | 1.160 | 10076.396 | 0 | live-simple-h2o-wrk |
| cached_reverse_proxy | native_simple_cached_proxy | haproxy_cached_reverse_proxy | wrk | measured | 2379.54 | 7369.92 | 0.323 | 0.537 | 0.161 | 7369.920 | 0 | live-simple-haproxy-wrk |
| cached_reverse_proxy | native_simple_cached_proxy | envoy_cached_reverse_proxy | wrk | measured | 1375.96 | 501.64 | 2.743 | 0.790 | 2.460 | 1375.960 | 0 | live-simple-envoy-wrk |
| upload_streaming_proxy | native_simple_upload_proxy | haproxy_upload_streaming_proxy | wrk | measured | 40.14 | 32.89 | 1.220 | 24.910 | 30.403 | 336.759 | 0 | live-simple-haproxy-upload-http |
| upgrade_tunnel_proxy | native_simple_upgrade_tunnel | haproxy_upgrade_tunnel_proxy | wrk | measured | 245.21 | 210.21 | 1.167 | 4.078 | 4.757 | 0.047 | 0 | live-simple-haproxy-tunnel-socket |
| dynamic_gpu_plaintext | native_simple_gpu_route_plaintext | cpu_simple_plaintext | wrk | measured | 1711.87 | 1963.95 | 0.872 | 0.980 | 0.705 | 1.006 | 0 | live-simple-cpu-gpu-route-wrk |
| dynamic_gpu_json | native_simple_gpu_route_json | cpu_simple_json | wrk | measured | 821.41 | 1073.76 | 0.765 | 1.400 | 1.160 | 1.100 | 0 | live-simple-cpu-gpu-route-wrk |
| reference_plaintext | native_simple_reference_plaintext | uwebsockets_plaintext | wrk | live-fixture-unavailable | 0 | 0 | 0 | 0 | 0 | 0 | 0 | reference-fixture-url-not-configured |
| reference_plaintext | native_simple_reference_plaintext | seastar_plaintext | wrk | live-fixture-unavailable | 0 | 0 | 0 | 0 | 0 | 0 | 0 | reference-fixture-url-not-configured |
