# Web Server NGINX Comparison Metrics

## Benchmark Normalization

| payload_policy | keepalive_policy | connections | threads | duration_seconds | worker_policy | logging_policy | cpu_affinity_policy |
|---|---|---:|---:|---:|---|---|---|
| same bytes per compared workload | wrk default keep-alive | 1 | 1 | 1 | one measured server worker unless wrapper overrides both sides | access logging disabled for measured hot path | not pinned on this host; report must say so |

| workload | simple_target | external_baseline | load_tool | status | simple_rps | external_rps | rps_ratio | simple_p99_ms | external_p99_ms | throughput_mbps | failures | reason | provenance |
|---|---|---|---|---|---:|---:|---:|---:|---:|---:|---:|---|---|
| static_1kb | native_simple_static_1024 | nginx_static_1024 | wrk | ready_unmeasured | 0 | 0 | 0 | 0 | 0 | 0 | 0 | run-live-simple-nginx-wrk-wrapper | unmeasured |
| static_1kb | native_simple_static_1024 | caddy_static_1024 | wrk | external-baseline-unavailable | 0 | 0 | 0 | 0 | 0 | 0 | 0 | caddy-not-installed | unmeasured |
| static_1kb | native_simple_static_1024 | h2o_static_1024 | wrk | external-baseline-unavailable | 0 | 0 | 0 | 0 | 0 | 0 | 0 | h2o-not-installed | unmeasured |
| static_1mb | native_simple_static_1048576 | nginx_static_1048576 | wrk | measured | 486.92 | 1369.65 | 0.356 | 2.620 | 0.756 | 11489.457 | 0 | live-simple-nginx-wrk | full-url-routed-native-simple |
| static_1mb | native_simple_static_1048576 | caddy_static_1048576 | wrk | external-baseline-unavailable | 0 | 0 | 0 | 0 | 0 | 0 | 0 | caddy-not-installed | unmeasured |
| static_1mb | native_simple_static_1048576 | h2o_static_1048576 | wrk | external-baseline-unavailable | 0 | 0 | 0 | 0 | 0 | 0 | 0 | h2o-not-installed | unmeasured |
| cached_reverse_proxy | native_simple_cached_proxy | haproxy_cached_reverse_proxy | wrk | measured | 2380.87 | 5978.68 | 0.398 | 0.575 | 1.820 | 5978.680 | 0 | live-simple-haproxy-wrk | legacy-unclassified |
| cached_reverse_proxy | native_simple_cached_proxy | envoy_cached_reverse_proxy | wrk | measured | 1391.83 | 457.14 | 3.045 | 0.860 | 4.290 | 1391.830 | 0 | live-simple-envoy-wrk | legacy-unclassified |
| upload_streaming_proxy | native_simple_upload_proxy | haproxy_upload_streaming_proxy | wrk | measured | 26.17 | 27.48 | 0.952 | 38.209 | 36.386 | 230.542 | 0 | live-simple-haproxy-upload-http | legacy-unclassified |
| upgrade_tunnel_proxy | native_simple_upgrade_tunnel | haproxy_upgrade_tunnel_proxy | wrk | measured | 285.64 | 204.29 | 1.398 | 3.501 | 4.895 | 0.055 | 0 | live-simple-haproxy-tunnel-socket | legacy-unclassified |
| dynamic_gpu_plaintext | native_simple_gpu_route_plaintext | cpu_simple_plaintext | wrk | measured | 1711.87 | 1963.95 | 0.872 | 0.980 | 0.705 | 1.006 | 0 | live-simple-cpu-gpu-route-wrk | legacy-unclassified |
| dynamic_gpu_json | native_simple_gpu_route_json | cpu_simple_json | wrk | measured | 821.41 | 1073.76 | 0.765 | 1.400 | 1.160 | 1.100 | 0 | live-simple-cpu-gpu-route-wrk | legacy-unclassified |
| reference_plaintext | native_simple_reference_plaintext | uwebsockets_plaintext | wrk | live-fixture-unavailable | 0 | 0 | 0 | 0 | 0 | 0 | 0 | reference-fixture-url-not-configured | unmeasured |
| reference_plaintext | native_simple_reference_plaintext | seastar_plaintext | wrk | live-fixture-unavailable | 0 | 0 | 0 | 0 | 0 | 0 | 0 | reference-fixture-url-not-configured | unmeasured |
