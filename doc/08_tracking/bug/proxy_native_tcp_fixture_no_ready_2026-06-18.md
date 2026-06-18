# Proxy Native TCP Fixture Does Not Reach Ready Marker

Date: 2026-06-18
Status: Fixed

## Summary

The GPU Web/DB external benchmark lane could not use the local Simple native
cached-proxy fixture because the live socket benchmark could not observe the
backend ready marker. This blocked using that fixture as evidence toward
measured Simple-vs-HAProxy/Envoy cached reverse-proxy rows.

Fixed on 2026-06-18 for the local live socket benchmark. The wrapper now builds
the Simple TCP backend and cached-proxy binaries with
`--runtime-bundle core-c-bootstrap`, which links the `rt_io_tcp_*` runtime
symbols needed by the fixture.

## Evidence

The source still type-checks:

```sh
bin/simple check \
  test/05_perf/web/proxy_live_native_backend.spl \
  test/05_perf/web/proxy_live_native_cached_proxy.spl
```

Before the fix, the live benchmark failed at runtime:

```sh
sh scripts/check/check-proxy-live-socket-benchmark.shs
```

Observed result:

```text
RuntimeError: missing marker [simple-proxy-native-backend-ready]; stdout=[]; stderr=
```

Debug evidence showed the default native-build lane left the socket externs
unresolved:

```text
U rt_io_tcp_bind
U rt_io_tcp_listen
```

Building the same backend with the core C runtime bundle linked the symbols and
reached readiness:

```text
0000000000403b99 T rt_io_tcp_bind
0000000000403d49 T rt_io_tcp_listen
[simple-proxy-native-backend-ready] addr=127.0.0.1:18191 requests=50
```

After updating `scripts/check/check-proxy-live-socket-benchmark.shs`, the
focused verification passes:

```sh
bin/simple check \
  test/05_perf/web/proxy_live_native_backend.spl \
  test/05_perf/web/proxy_live_native_cached_proxy.spl

sh scripts/check/check-proxy-live-socket-benchmark.shs
```

```text
STATUS: PASS proxy live socket benchmark
```

## Impact

`doc/03_plan/perf/gpu_web_db_offload_optimization_benchmark_plan.md` still
requires live Simple proxy fixture URLs before the external suite can produce
cached reverse-proxy rows against HAProxy/Envoy. The current generated
HAProxy/Envoy fixtures point to `host.docker.internal:8090`, but there is no
validated long-running Simple cached-proxy fixture listening there yet.

## Next Step

Use the fixed local native TCP proxy fixture as the basis for a sustained
external-suite cached reverse-proxy endpoint on the generated fixture port, then
rerun:

```sh
SIMPLE_CACHED_PROXY_URL=http://127.0.0.1:8090/cacheable \
HAPROXY_CACHED_PROXY_URL=http://127.0.0.1:8091/cacheable \
ENVOY_CACHED_PROXY_URL=http://127.0.0.1:8092/cacheable \
sh scripts/check/check-web-server-proxy-external-live-compare.shs
```
