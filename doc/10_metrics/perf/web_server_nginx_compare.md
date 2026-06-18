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
| cached_reverse_proxy | native_simple_cached_proxy | haproxy_cached_reverse_proxy | wrk | measured | 2510.70 | 7463.72 | 0.336 | 0.558 | 0.163 | 7463.720 | 0 | live-simple-haproxy-wrk |
| cached_reverse_proxy | native_simple_cached_proxy | envoy_cached_reverse_proxy | wrk | measured | 1420.12 | 471.71 | 3.011 | 0.844 | 3.070 | 1420.120 | 0 | live-simple-envoy-wrk |
| upload_streaming_proxy | native_simple_upload_proxy | haproxy_upload_streaming_proxy | wrk | measured | 37.48 | 37.56 | 0.998 | 26.683 | 26.624 | 315.075 | 0 | live-simple-haproxy-upload-http |
| upgrade_tunnel_proxy | native_simple_upgrade_tunnel | haproxy_upgrade_tunnel_proxy | wrk | measured | 240.86 | 173.32 | 1.390 | 4.152 | 5.770 | 0.046 | 0 | live-simple-haproxy-tunnel-socket |
| dynamic_gpu_plaintext | native_simple_gpu_route_plaintext | cpu_simple_plaintext | wrk | live-fixture-unavailable | 0 | 0 | 0 | 0 | 0 | 0 | 0 | dynamic-gpu-route-live-server-not-configured |
| dynamic_gpu_json | native_simple_gpu_route_json | cpu_simple_json | wrk | live-fixture-unavailable | 0 | 0 | 0 | 0 | 0 | 0 | 0 | dynamic-gpu-route-live-server-not-configured |
| reference_plaintext | native_simple_reference_plaintext | uwebsockets_plaintext | wrk | live-fixture-unavailable | 0 | 0 | 0 | 0 | 0 | 0 | 0 | reference-fixture-url-not-configured |
| reference_plaintext | native_simple_reference_plaintext | seastar_plaintext | wrk | live-fixture-unavailable | 0 | 0 | 0 | 0 | 0 | 0 | 0 | reference-fixture-url-not-configured |
