# Proxy Native TCP Fixture Does Not Reach Ready Marker

Date: 2026-06-18
Status: Open

## Summary

The GPU Web/DB external benchmark lane cannot fill the live Simple cached-proxy
URL from the current native proxy fixture. The existing source checks and native
builds, but the live socket benchmark cannot observe the backend ready marker.
This blocks measured Simple-vs-HAProxy/Envoy cached reverse-proxy rows.

## Evidence

The source still type-checks and links:

```sh
bin/simple check \
  test/05_perf/web/proxy_live_native_backend.spl \
  test/05_perf/web/proxy_live_native_cached_proxy.spl
```

But the live benchmark fails at runtime:

```sh
sh scripts/check/check-proxy-live-socket-benchmark.shs
```

Observed result:

```text
RuntimeError: missing marker [simple-proxy-native-backend-ready]; stdout=[]; stderr=
```

A fixed-port external cached-proxy experiment for the GPU Web/DB lane also
failed before readiness when native-built. Running the same backend source
through the interpreter returned:

```text
[simple-proxy-external-backend-error] listen
```

## Impact

`doc/03_plan/perf/gpu_web_db_offload_optimization_benchmark_plan.md` still
requires live Simple proxy fixture URLs before the external suite can produce
cached reverse-proxy rows against HAProxy/Envoy. The current generated
HAProxy/Envoy fixtures point to `host.docker.internal:8090`, but there is no
validated Simple cached-proxy fixture listening there.

## Next Step

Fix or replace the Simple native TCP proxy fixture so it can serve a sustained
cached reverse-proxy endpoint, then rerun:

```sh
sh scripts/check/check-proxy-live-socket-benchmark.shs
```

After that passes, start the Simple fixture on the external-suite upstream port
and rerun:

```sh
SIMPLE_CACHED_PROXY_URL=http://127.0.0.1:8090/cacheable \
HAPROXY_CACHED_PROXY_URL=http://127.0.0.1:8091/cacheable \
ENVOY_CACHED_PROXY_URL=http://127.0.0.1:8092/cacheable \
sh scripts/check/check-web-server-proxy-external-live-compare.shs
```
