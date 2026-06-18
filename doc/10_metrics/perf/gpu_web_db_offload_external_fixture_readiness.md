# GPU Web/DB External Fixture Readiness Metrics

## Bootstrap Status

| bootstrap check | status | reason |
|---|---|---|
| bootstrap_container_runtime | ready | docker:/usr/bin/docker |
| bootstrap_container_engine | ready | docker-info |
| bootstrap_package_manager | ready | apt:/usr/bin/apt |
| bootstrap_compose | optional-missing | docker-compose-not-installed |
| bootstrap_missing_fixture_items | info | 29 |
| bootstrap_local_fixture_bootstrap | possible | container-engine-ready |
| bootstrap_side_effects | none | status-only-no-install-no-container-start |

## Fixtures

| fixture | status | reason |
|---|---|---|
| wrk | ready | /usr/bin/wrk |
| nginx | ready | /usr/sbin/nginx |
| caddy | missing | caddy-not-installed |
| h2o | missing | h2o-not-installed |
| haproxy | missing | haproxy-not-installed |
| envoy | missing | envoy-not-installed |
| clickhouse | missing | clickhouse-not-installed |
| duckdb | missing | duckdb-not-installed-or-DUCKDB_IMAGE-not-configured |
| psql | missing | psql-not-installed |
| pgbench | missing | pgbench-not-installed |
| mongodb | missing | mongodb-not-installed |
| redis_valkey | missing | redis_valkey-not-installed |
| redis_benchmark | missing | redis_benchmark-not-installed |
| simple_cached_proxy_url | missing | SIMPLE_CACHED_PROXY_URL-not-configured |
| haproxy_cached_proxy_url | missing | HAPROXY_CACHED_PROXY_URL-not-configured |
| envoy_cached_proxy_url | missing | ENVOY_CACHED_PROXY_URL-not-configured |
| simple_upload_proxy_url | missing | SIMPLE_UPLOAD_PROXY_URL-not-configured |
| haproxy_upload_proxy_url | missing | HAPROXY_UPLOAD_PROXY_URL-not-configured |
| simple_tunnel_proxy_url | missing | SIMPLE_TUNNEL_PROXY_URL-not-configured |
| haproxy_tunnel_proxy_url | missing | HAPROXY_TUNNEL_PROXY_URL-not-configured |
| dynamic_gpu_plaintext_url | missing | DYNAMIC_GPU_PLAINTEXT_URL-not-configured |
| dynamic_cpu_plaintext_url | missing | DYNAMIC_CPU_PLAINTEXT_URL-not-configured |
| dynamic_gpu_json_url | missing | DYNAMIC_GPU_JSON_URL-not-configured |
| dynamic_cpu_json_url | missing | DYNAMIC_CPU_JSON_URL-not-configured |
| simple_reference_plaintext_url | missing | SIMPLE_REFERENCE_PLAINTEXT_URL-not-configured |
| uwebsockets_plaintext_url | missing | UWEBSOCKETS_PLAINTEXT_URL-not-configured |
| seastar_plaintext_url | missing | SEASTAR_PLAINTEXT_URL-not-configured |
| clickhouse_url | missing | CLICKHOUSE_URL-not-configured |
| postgres_url | missing | POSTGRES_URL-not-configured |
| mongo_url | missing | MONGO_URL-not-configured |
| redis_url | missing | REDIS_URL-not-configured |
