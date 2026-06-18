# Web Server NGINX Comparison Metrics

## Benchmark Normalization

| payload_policy | keepalive_policy | connections | threads | duration_seconds | worker_policy | logging_policy | cpu_affinity_policy |
|---|---|---:|---:|---:|---|---|---|
| same bytes per compared workload | wrk default keep-alive | 1 | 1 | 1 | one measured server worker unless wrapper overrides both sides | access logging disabled for measured hot path | not pinned on this host; report must say so |

| workload | simple_target | external_baseline | load_tool | status | simple_rps | external_rps | rps_ratio | simple_p99_ms | external_p99_ms | throughput_mbps | failures | reason |
|---|---|---|---|---|---:|---:|---:|---:|---:|---:|---:|---|
| static_1kb | native_simple_static_1024 | nginx_static_1024 | wrk | measured | 2551.83 | 15460.12 | 0.165 | 0.449 | 0.090 | 126.649 | 0 | live-simple-nginx-wrk |
| static_1kb | native_simple_static_1024 | caddy_static_1024 | wrk | measured | 2641.07 | 3533.34 | 0.747 | 0.444 | 0.372 | 28.945 | 0 | live-simple-caddy-wrk |
| static_1kb | native_simple_static_1024 | h2o_static_1024 | wrk | external-baseline-unavailable | 0 | 0 | 0 | 0 | 0 | 0 | 0 | h2o-not-installed |
| static_1mb | native_simple_static_1048576 | nginx_static_1048576 | wrk | measured | 835.83 | 1380.71 | 0.605 | 1.600 | 1.170 | 11582.235 | 0 | live-simple-nginx-wrk |
| static_1mb | native_simple_static_1048576 | caddy_static_1048576 | wrk | measured | 863.73 | 1338.52 | 0.645 | 1.360 | 1.110 | 11228.320 | 0 | live-simple-caddy-wrk |
| static_1mb | native_simple_static_1048576 | h2o_static_1048576 | wrk | external-baseline-unavailable | 0 | 0 | 0 | 0 | 0 | 0 | 0 | h2o-not-installed |
| cached_reverse_proxy | native_simple_cached_proxy | haproxy_cached_reverse_proxy | wrk | external-baseline-unavailable | 0 | 0 | 0 | 0 | 0 | 0 | 0 | haproxy-not-installed |
| cached_reverse_proxy | native_simple_cached_proxy | envoy_cached_reverse_proxy | wrk | external-baseline-unavailable | 0 | 0 | 0 | 0 | 0 | 0 | 0 | envoy-not-installed |
| upload_streaming_proxy | native_simple_upload_proxy | haproxy_upload_streaming_proxy | wrk | external-baseline-unavailable | 0 | 0 | 0 | 0 | 0 | 0 | 0 | haproxy-not-installed |
| upgrade_tunnel_proxy | native_simple_upgrade_tunnel | haproxy_upgrade_tunnel_proxy | wrk | external-baseline-unavailable | 0 | 0 | 0 | 0 | 0 | 0 | 0 | haproxy-not-installed |
| dynamic_gpu_plaintext | native_simple_gpu_route_plaintext | cpu_simple_plaintext | wrk | live-fixture-unavailable | 0 | 0 | 0 | 0 | 0 | 0 | 0 | dynamic-gpu-route-live-server-not-configured |
| dynamic_gpu_json | native_simple_gpu_route_json | cpu_simple_json | wrk | live-fixture-unavailable | 0 | 0 | 0 | 0 | 0 | 0 | 0 | dynamic-gpu-route-live-server-not-configured |
| reference_plaintext | native_simple_reference_plaintext | uwebsockets_plaintext | wrk | live-fixture-unavailable | 0 | 0 | 0 | 0 | 0 | 0 | 0 | reference-fixture-url-not-configured |
| reference_plaintext | native_simple_reference_plaintext | seastar_plaintext | wrk | live-fixture-unavailable | 0 | 0 | 0 | 0 | 0 | 0 | 0 | reference-fixture-url-not-configured |
