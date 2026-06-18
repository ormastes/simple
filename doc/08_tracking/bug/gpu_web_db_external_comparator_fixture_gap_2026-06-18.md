# GPU Web/DB Strict Suite Still Lacks Real External Comparator URLs

Date: 2026-06-18
Status: Open
Lane: gpu_web_db_offload

## Summary

The GPU Web/DB benchmark lane has a passing repo-local required suite, but the
strict external suite still cannot be used for fastest-server parity claims.
The default fixture environment is intentionally empty for live proxy,
dynamic-route, and optional reference comparator URLs.

Current strict status:

```sh
sh scripts/check/check-gpu-web-db-offload-external-suite.shs --status
```

```text
external-suite-status=missing_fixture_items|14
external-suite-status=required_missing_fixture_items|11
external-suite-status=optional_missing_fixture_items|3
external-suite-status=verdict|WAITING_ON_FIXTURES
external-suite-status=required_verdict|WAITING_ON_REQUIRED_FIXTURES
```

The missing required items are the selected fixture URLs for cached proxy,
upload proxy, tunnel proxy, and dynamic CPU/GPU plaintext/JSON routes. The
missing optional items are the real plaintext reference comparator URLs for
Simple, uWebSockets, and Seastar.

## Why This Matters

The repo-local required suite proves the local Simple/proxy/dynamic/DB fixture
wiring and report regeneration path:

```sh
sh scripts/check/check-gpu-web-db-offload-local-required-suite.shs
```

That is valid required-suite evidence, but it is not a substitute for real
uWebSockets or Seastar comparator services. Fastest-server claims require the
strict suite to run with production-shape comparator endpoints and the real
external reference URLs filled.

## Expected

A completed strict external comparator lane should provide:

- real `SIMPLE_CACHED_PROXY_URL`, `HAPROXY_CACHED_PROXY_URL`, and
  `ENVOY_CACHED_PROXY_URL` endpoints for cached proxy rows.
- real `SIMPLE_UPLOAD_PROXY_URL`, `HAPROXY_UPLOAD_PROXY_URL`,
  `SIMPLE_TUNNEL_PROXY_URL`, and `HAPROXY_TUNNEL_PROXY_URL` endpoints.
- real `DYNAMIC_GPU_PLAINTEXT_URL`, `DYNAMIC_CPU_PLAINTEXT_URL`,
  `DYNAMIC_GPU_JSON_URL`, and `DYNAMIC_CPU_JSON_URL` endpoints.
- real `SIMPLE_REFERENCE_PLAINTEXT_URL`, `UWEBSOCKETS_PLAINTEXT_URL`, and
  `SEASTAR_PLAINTEXT_URL` endpoints with workload parity.
- real `UWEBSOCKETS_PLAINTEXT_PROVENANCE` and
  `SEASTAR_PLAINTEXT_PROVENANCE` values identifying the comparator binary,
  container image, or source commit. URL-only placeholders must remain blocked.
- a strict readiness pass:

```text
STATUS: PASS gpu web/db external suite require-ready
```

## Acceptance

- `sh scripts/check/check-gpu-web-db-offload-external-suite.shs --require-ready`
  passes with real comparator URLs.
- `scripts/check/check-web-server-proxy-external-live-compare.shs` emits
  measured rows for cached proxy, upload, tunnel, and reference plaintext
  comparators.
- `scripts/check/check-web-server-dynamic-gpu-route-compare.shs` emits measured
  rows for dynamic plaintext and JSON CPU/GPU route pairs.
- The generated reports clearly distinguish scoped local fixture evidence from
  real fastest-server comparator evidence.
