# GPU Web/DB External Fixture Readiness Metrics

## Bootstrap Status

| bootstrap check | status | reason |
|---|---|---|
| bootstrap_container_runtime | ready | docker:/usr/bin/docker |
| bootstrap_container_engine | ready | docker-info |
| bootstrap_package_manager | ready | apt:/usr/bin/apt |
| bootstrap_compose | optional-missing | docker-compose-not-installed |
| bootstrap_missing_fixture_items | info | 15 |
| bootstrap_local_fixture_bootstrap | possible | container-engine-ready |
| bootstrap_side_effects | none | status-only-no-install-no-container-start |

## Fixtures

| fixture | status | reason |
|---|---|---|
| wrk | ready | /usr/bin/wrk |
| nginx | ready | /usr/sbin/nginx |
| caddy | ready | caddy-ready:docker-container:gpu-web-db-caddy-static:caddy |
| h2o | ready | h2o-ready:docker-container:gpu-web-db-h2o-static:h2o |
| haproxy | ready | haproxy-ready:docker-container:gpu-web-db-haproxy-cached-proxy:haproxy |
| envoy | ready | envoy-ready:docker-container:gpu-web-db-envoy-cached-proxy:envoy |
| clickhouse | ready | clickhouse-ready:docker-container:gpu-web-db-clickhouse-olap:clickhouse |
| duckdb | missing | duckdb-not-installed |
| psql | ready | psql-ready:docker-container:gpu-web-db-postgres-tpch:psql |
| pgbench | ready | pgbench-ready:docker-container:gpu-web-db-postgres-tpch:pgbench |
| mongodb | ready | mongodb-ready:docker-container:gpu-web-db-mongo-ycsb:mongosh |
| redis_valkey | ready | redis-valkey-ready:docker-container:gpu-web-db-redis-valkey-kv:redis-cli |
| redis_benchmark | ready | redis-benchmark-ready:docker-container:gpu-web-db-redis-valkey-kv:redis-benchmark |
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
| clickhouse_url | ready | CLICKHOUSE_URL-configured |
| postgres_url | ready | POSTGRES_URL-configured |
| mongo_url | ready | MONGO_URL-configured |
| redis_url | ready | REDIS_URL-configured |
