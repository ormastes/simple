<!-- codex-impl -->
# GPU Web and DB Offload Implementation Status

Status: implementation in progress; benchmark harness contracts are in place,
external fixture coverage remains incomplete.

Current Benchmark Recovery State (2026-06-17):

- Crash-session continuation was traced to
  `/home/ormastes/.codex/sessions/2026/06/16/rollout-2026-06-16T04-07-18-019ece9c-bb30-76a1-952f-7233322187d1.jsonl`.
  The current authoritative state is the worktree benchmark plan and recovery
  harness artifacts, because the lane has advanced past the original recovered
  crash note.
- The remade benchmark plan in
  `doc/03_plan/perf/gpu_web_db_offload_optimization_benchmark_plan.md` now
  distinguishes implemented harness infrastructure from remaining external
  measurement blockers.
- Implemented harness infrastructure includes NGINX static measured rows,
  optional Caddy/H2O static producer rows, web measured-row producer/consumer
  contracts, dynamic-route producer contracts, DB external-baseline
  producer/consumer contracts, report auto-consumption of producer files, and
  explicit unavailable rows for missing web and DB baselines.
- NGINX is the only fastest-server-style external baseline with measured rows
  on this host. Redis/Valkey-style key/value server comparisons are not
  implemented or measured; current DB external baseline coverage is limited to
  ClickHouse, DuckDB, PostgreSQL, and MongoDB/YCSB status/measured-row
  contracts.
- `scripts/check/check-gpu-web-db-offload-external-fixture-readiness.shs`
  reports the remaining external fixture/tool readiness in one host-safe gate
  and writes durable artifacts to
  `doc/09_report/perf/gpu_web_db_offload_external_fixture_readiness_2026-06-17.md`
  and `doc/10_metrics/perf/gpu_web_db_offload_external_fixture_readiness.md`;
  `--self-test-artifacts` validates artifact generation with temporary paths.
  The generated report now includes category totals for core load tools,
  web/proxy tools, DB tools, proxy fixture URLs, dynamic-route URLs, and DB
  service URLs so the next fixture setup step can target the right blocker
  class. `--missing-by-category`
  prints the same blocker sets as machine-readable `category=item,item` lines,
  and `--write-missing-by-category` writes them to
  `build/perf/gpu_web_db_offload/external-fixture-missing-by-category.env`.
  The env-file variants `--missing-by-category-from-env-file` and
  `--write-missing-by-category-from-env-file` import non-empty readiness URL
  values from `build/perf/gpu_web_db_offload/external-fixtures.env` before
  computing those categories.
  `--print-env-template` prints the live cached-proxy, upload/tunnel proxy,
  dynamic-route, and DB baseline URL contract needed to turn the remaining
  URL-backed fixture rows into ready rows, and `--write-env-template` writes
  the same handoff file to
  `build/perf/gpu_web_db_offload/external-fixtures.env`. The generated env file
  is safe by default: URL variables are empty until explicitly filled, so
  sourcing the untouched template does not mark URL-backed rows ready.
  `--check-env-file` sources the env file and re-runs readiness so filled URL
  values can be validated before live producers run.
  `--print-setup-checklist` and `--write-setup-checklist` provide the matching
  tool/service setup checklist for the missing web, proxy, and DB baselines;
  the default checklist path is
  `build/perf/gpu_web_db_offload/external-fixture-setup-checklist.md`. That
  generated checklist now includes the external suite `--refresh-status` and
  `--preflight` commands before the guarded full external suite command, plus
  explicit `--allow-partial` for local artifact refresh while fixtures remain
  missing. Partial mode ends with WARN so it cannot be mistaken for a
  fixture-ready full-suite PASS.
  `--print-env-hints` and `--write-env-hints` provide a non-sourceable Markdown
  handoff at
  `build/perf/gpu_web_db_offload/external-fixture-env-hints.md` with localhost
  URL examples derived from the generated proxy and DB fixture templates.
  `--print-runbook` and `--write-runbook` provide the matching operator command
  sequence at `build/perf/gpu_web_db_offload/external-fixture-runbook.md`;
  generation is side-effect-free and does not start containers or benchmarks.
  `--print-docker-run-template` and `--write-docker-run-template` provide an
  executable Docker fallback template at
  `build/perf/gpu_web_db_offload/external-fixture-docker-run.shs` for hosts
  that have Docker but lack Docker Compose. The generated Compose and
  docker-run proxy fixtures map `host.docker.internal` to Docker's
  `host-gateway`, which keeps the HAProxy/Envoy upstream defaults usable on
  Linux Docker hosts when the repo-local Simple proxy fixture listens on the
  host. The docker-run fallback is restart-safe for its generated fixture names:
  it removes and recreates only its own `gpu-web-db-*` containers. Bootstrap
  status detects both Docker Compose v2 (`docker compose`) and the legacy
  `docker-compose` binary before reporting Compose as optional-missing, and
  prints `bootstrap_container_engine` so a present container CLI is not mistaken
  for a usable engine. The local fixture bootstrap summary reports `possible`
  only when that engine probe is ready; otherwise a present but unusable
  runtime reports `engine-unavailable`. The engine-status classifier has a
  host-safe self-test for ready, unavailable, missing, and unknown runtime
  states. The durable readiness report and metrics table include a separate
  `Bootstrap Status` section.
- `scripts/check/check-gpu-web-db-offload-recovery-harness-self-tests.shs`
  checks shell syntax and aggregates the host-safe parser, producer, and
  readiness self-tests for quick crash-session recovery without rerunning live
  benchmarks. It writes
  `doc/09_report/perf/gpu_web_db_offload_recovery_harness_self_tests_2026-06-17.md`
  and `doc/10_metrics/perf/gpu_web_db_offload_recovery_harness_self_tests.md`;
  `--self-test-artifacts` validates the same artifact path with temporary
  outputs, `--self-test-env-template`, `--self-test-write-env-template`,
  `--self-test-env-template-safe-defaults`, `--self-test-check-env-file`,
  `--self-test-container-engine-status`, `--self-test-category-summary`,
  `--self-test-missing-by-category`,
  `--self-test-write-missing-by-category`, `--self-test-setup-checklist`, and
  `--self-test-write-setup-checklist` validate the fixture setup contract, and
  `--check-current-artifacts` verifies that the current durable report/metrics
  files still contain measured NGINX rows, external DB baseline status rows,
  readiness fixture lists, recovery passed-gate evidence, and the durable
  fixture handoff files under `build/perf/gpu_web_db_offload/`.
- Remaining blockers are external-state requirements: Caddy/H2O, HAProxy,
  Envoy, live CPU/GPU dynamic route URLs, ClickHouse, DuckDB,
  PostgreSQL/pgbench, MongoDB shell access, and any additional Seastar or
  uWebSockets reference fixtures.

## 2026-06-17 Optional Caddy/H2O Static Producer Note

The external static-server lane now has a sibling measured producer for Caddy
and H2O:

- `scripts/check/check-web-server-static-external-live-compare.shs` reuses the
  native Simple static-file fixture and `wrk` parser shape from the NGINX live
  wrapper.
- On hosts without Caddy or H2O it exits cleanly with
  `STATUS: WARN tool-unavailable:caddy,h2o`, preserving the report's explicit
  unavailable rows.
- On hosts with either tool installed, it emits strict
  `WEB_SERVER_EXTERNAL_COMPARE_MEASURED=...` rows to
  `build/perf/web_server_nginx_compare/static-external-measured-rows.env`.
- `scripts/check/check-web-server-nginx-compare-report.shs` now auto-consumes
  that producer file alongside the NGINX and dynamic-route producer files.
- Evidence refreshed:
  `sh -n scripts/check/check-web-server-static-external-live-compare.shs`
  passes,
  `sh scripts/check/check-web-server-static-external-live-compare.shs --self-test-static-external-parser`
  prints `STATUS: PASS static external parser self-test`,
  `sh scripts/check/check-web-server-static-external-live-compare.shs --self-test-static-external-producer-lines`
  prints `STATUS: PASS static external producer self-test`,
  `sh scripts/check/check-web-server-nginx-compare-report.shs --self-test-external-web-measured-parser`
  prints `STATUS: PASS external web measured parser self-test`, and
  `sh scripts/check/check-web-server-static-external-live-compare.shs` prints
  `STATUS: WARN tool-unavailable:caddy,h2o` on this host.

## 2026-06-17 Optional HAProxy/Envoy Cached Proxy Producer Note

The external proxy comparison lane now has a URL-driven measured producer for
cached reverse-proxy baselines:

- `scripts/check/check-web-server-proxy-external-live-compare.shs` measures
  configured `SIMPLE_CACHED_PROXY_URL` against `HAPROXY_CACHED_PROXY_URL` and/or
  `ENVOY_CACHED_PROXY_URL` with `wrk`.
- The same wrapper measures configured `SIMPLE_UPLOAD_PROXY_URL` against
  `HAPROXY_UPLOAD_PROXY_URL` with an HTTP upload request helper, and configured
  `SIMPLE_TUNNEL_PROXY_URL` against `HAPROXY_TUNNEL_PROXY_URL` with a raw
  Upgrade/tunnel echo helper.
- The wrapper emits strict `WEB_SERVER_EXTERNAL_COMPARE_MEASURED=...` rows to
  `build/perf/web_server_nginx_compare/proxy-external-measured-rows.env`, which
  `scripts/check/check-web-server-nginx-compare-report.shs` now auto-consumes.
- On this host it exits cleanly with
  `STATUS: WARN live-fixture-unavailable:proxy-external-urls-not-configured`
  because no live proxy fixture URLs are configured.
- The producer self-test validates the HAProxy cached, Envoy cached, HAProxy
  upload, and HAProxy tunnel measured-line shapes so all proxy rows use the
  same report contract instead of separate tables.
- `scripts/check/check-gpu-web-db-offload-external-fixture-readiness.shs` now
  tracks the matching URL handoff variables:
  `SIMPLE_CACHED_PROXY_URL`, `HAPROXY_CACHED_PROXY_URL`,
  `ENVOY_CACHED_PROXY_URL`, `SIMPLE_UPLOAD_PROXY_URL`,
  `HAPROXY_UPLOAD_PROXY_URL`, `SIMPLE_TUNNEL_PROXY_URL`, and
  `HAPROXY_TUNNEL_PROXY_URL`. They are included in the safe-default env
  template, setup checklist, readiness report, and `proxy_fixture_urls`
  missing-category output.
- Evidence refreshed:
  `sh -n scripts/check/check-web-server-proxy-external-live-compare.shs` passes,
  `sh scripts/check/check-web-server-proxy-external-live-compare.shs --self-test-proxy-external-producer-lines`
  prints `STATUS: PASS proxy external producer self-test`,
  `sh scripts/check/check-web-server-nginx-compare-report.shs --self-test-external-web-measured-parser`
  prints `STATUS: PASS external web measured parser self-test`, and
  `sh scripts/check/check-web-server-proxy-external-live-compare.shs` prints
  `STATUS: WARN live-fixture-unavailable:proxy-external-urls-not-configured`.

## 2026-06-17 Reverse-Proxy Production Hardening Evidence Note

The crash-session follow-on plan has been remade in
`doc/03_plan/agent_tasks/gpu_web_db_offload.md`: the next lane is production
hardening evidence rather than another crash retry. The first implementation
slice adds pure async reverse-proxy evidence for timeout state, request/upload
backpressure, downstream response backpressure, upstream pool pressure, and
throughput bytes/sec:

- `src/lib/nogc_async_mut/http_server/proxy.spl` now exposes
  `AsyncProxyProductionHardeningEvidence`,
  `async_proxy_connection_production_hardening`,
  `async_proxy_connection_throughput_bytes_per_sec`,
  `async_proxy_pool_stressed`, and the low-level throughput/evidence helpers.
- `src/lib/nogc_async_mut/http_server/__init__.spl` re-exports the production
  hardening boundary through `std.http_server` for worker/report consumers.
- `src/lib/nogc_async_mut/http_server/worker.spl` records the latest production
  hardening evidence before proxy cleanup or upstream pool release removes the
  active proxy state.
- `test/01_unit/lib/nogc_async_mut/http_server/async_reverse_proxy_spec.spl`
  covers healthy throughput evidence, timeout priority, request backpressure,
  response backpressure, pool stress, and the package-root export path.
- Evidence refreshed:
  `bin/simple check src/lib/nogc_async_mut/http_server/proxy.spl src/lib/nogc_async_mut/http_server/__init__.spl test/01_unit/lib/nogc_async_mut/http_server/async_reverse_proxy_spec.spl`,
  `simple check src/lib/nogc_async_mut/http_server/proxy.spl src/lib/nogc_async_mut/http_server/__init__.spl src/lib/nogc_async_mut/http_server/worker.spl test/01_unit/lib/nogc_async_mut/http_server/async_reverse_proxy_spec.spl`,
  `SIMPLE_LIB=src bin/simple test test/01_unit/lib/nogc_async_mut/http_server/async_reverse_proxy_spec.spl --mode=interpreter --clean`,
  and `SIMPLE_LIB=src bin/simple spipe-docgen test/01_unit/lib/nogc_async_mut/http_server/async_reverse_proxy_spec.spl --output doc/06_spec --no-index`.
  The final focused test passed with 99 tests; docgen completed with the
  pre-existing short-doc/export/generic warnings.

## 2026-06-17 Reverse-Proxy Benchmark Hardening Row Note

The production hardening evidence is now part of the host-safe proxy benchmark
report path:

- `test/05_perf/web/proxy_reverse_proxy_bench_spec.spl` adds
  `async_proxy_hardening_evidence_100`, which measures the new timeout,
  request backpressure, response backpressure, pool-pressure, and throughput
  evidence boundary without opening sockets.
- `doc/06_spec/test/05_perf/web/proxy_reverse_proxy_bench_spec.md` was
  regenerated and includes the new hardening row.
- `scripts/check/check-proxy-benchmark-report.shs` now requires the hardening
  row in generated docs and uses `SIMPLE_BIN`/`simple` fallback when
  `bin/simple` is not present.
- `scripts/check/check-proxy-live-socket-benchmark.shs` uses the same
  `SIMPLE_BIN`/`simple` fallback for its native live-socket subgate.
- Evidence refreshed:
  `sh scripts/check/check-proxy-benchmark-report.shs` now prints
  `STATUS: PASS proxy live socket benchmark` and
  `STATUS: PASS proxy benchmark report`.

## 2026-06-17 Production DB/Web Runtime Queue Throughput Note

The GPU Web/DB benchmark lane now includes a combined production-facing
runtime-queue throughput contract row:

- `test/05_perf/web_db_offload/gpu_web_db_offload_bench_spec.spl` adds
  `production_db_web_runtime_queue_throughput_contract`, aggregating the DBFS
  SSD materialized scan runtime-queue row and the web-framework inference
  runtime-queue row into one validated DB+web throughput contract.
- The web-framework runtime queue fixture now emits on the valid host GPU queue
  lane (`rt_host_gpu_queue_emit(2, 1, ...)`), matching the host GPU lane
  contract and restoring backend timing validation for that row.
- `scripts/check/check-gpu-web-db-offload-benchmark-report.shs` now falls back
  from `src/compiler_rust/target/debug/simple`/`bin/simple` to `simple` on
  `PATH`, requires the combined row in generated docs, writes it to the report
  and metrics table, and validates it in the generated report.
- Evidence refreshed:
  `sh scripts/check/check-gpu-web-db-offload-benchmark-report.shs` passes with
  13 examples and prints `STATUS: PASS gpu web/db offload benchmark report`.
  This remains a bounded runtime-queue throughput contract row, not an external
  workload speedup claim.

## 2026-06-17 External NGINX Comparison Readiness Note

The external-comparison lane now has a concrete Simple-vs-NGINX report gate:

- `test/05_perf/web_server_nginx_compare/external_compare_report.spl` defines
  host-safe tool availability and comparison row contracts.
- `test/05_perf/web_server_nginx_compare/external_compare_report_spec.spl`
  proves ready, unavailable-load-tool, unavailable-baseline, markdown, and
  no-speedup-claim behavior.
- `scripts/check/check-web-server-nginx-compare-report.shs` runs the contract,
  generates
  `doc/06_spec/test/05_perf/web_server_nginx_compare/external_compare_report_spec.md`,
  and writes `doc/09_report/perf/web_server_nginx_compare_2026-06-17.md` plus
  `doc/10_metrics/perf/web_server_nginx_compare.md`.
- On this host the report records `/usr/sbin/nginx` and `/usr/bin/wrk` as
  available and emits `ready_unmeasured` Simple-vs-NGINX rows for 1 KiB and
  1 MiB static workloads. These rows prove readiness/report shape only; they
  intentionally do not claim Simple speedup.
- Evidence refreshed:
  `sh scripts/check/check-web-server-nginx-compare-report.shs` prints
  `STATUS: PASS web server nginx comparison report`.

## 2026-06-17 External NGINX Live Measurement Note

The readiness rows now have a measured live follow-up:

- `test/05_perf/web_server_nginx_compare/live_static_native_server.spl`
  provides a native Simple static-file target using the same low-level TCP
  native pattern as the green proxy live fixtures.
- `scripts/check/check-web-server-nginx-live-compare.shs` native-builds that
  target, starts an isolated local NGINX baseline, runs `wrk --latency` against
  1 KiB and 1 MiB static payloads, and rewrites
  `doc/09_report/perf/web_server_nginx_compare_2026-06-17.md` plus
  `doc/10_metrics/perf/web_server_nginx_compare.md` with measured rows.
- Measured host evidence:
  - `static_1kb`: Simple 2120.72 RPS vs NGINX 13742.27 RPS, ratio 0.154,
    p99 0.628 ms vs 0.093 ms, failures 0.
  - `static_1mb`: Simple 736.16 RPS vs NGINX 762.85 RPS, ratio 0.965,
    p99 1.770 ms vs 1.850 ms, failures 0.
- Evidence refreshed:
  `sh scripts/check/check-web-server-nginx-live-compare.shs` prints
  `STATUS: PASS web server nginx live comparison`.

These rows provide live RPS/latency evidence only. They do not claim Simple is
faster than NGINX; the 1 KiB row is below NGINX and the 1 MiB row is near
parity on this host.

## 2026-06-17 External Missing-Baseline Row Note

The external-comparison report now records missing baseline tools explicitly
instead of silently skipping them:

- `test/05_perf/web_server_nginx_compare/external_compare_report.spl` adds a
  named `external_unavailable_baseline_row` contract.
- `scripts/check/check-web-server-nginx-compare-report.shs` detects `nginx`,
  `wrk`, `haproxy`, `envoy`, `caddy`, and `h2o`, preserves existing measured
  NGINX rows from the live wrapper, and appends unavailable-baseline rows for
  missing static/proxy baselines.
- `--self-test-tool-row-classification` verifies the report-script row
  classifier without rewriting reports: missing `wrk` becomes
  `load-tool-unavailable`, missing baseline tools become
  `external-baseline-unavailable`, and installed baseline plus `wrk` becomes
  `ready_unmeasured` with no measured values.
- The generated report now contains:
  - measured NGINX rows for `static_1kb` and `static_1mb`;
  - unavailable Caddy/H2O static rows;
  - unavailable HAProxy/Envoy cached reverse-proxy rows;
  - unavailable HAProxy upload-streaming and upgrade-tunnel rows.
- Evidence refreshed:
  `simple check test/05_perf/web_server_nginx_compare/external_compare_report.spl test/05_perf/web_server_nginx_compare/external_compare_report_spec.spl`
  passes,
  `sh scripts/check/check-web-server-nginx-compare-report.shs --self-test-tool-row-classification`
  prints `STATUS: PASS web comparison tool row classification self-test`, and
  `sh scripts/check/check-web-server-nginx-compare-report.shs`
  prints `STATUS: PASS web server nginx comparison report`.

## 2026-06-17 Dynamic GPU Route HTTP Matrix Note

The external HTTP comparison matrix now includes the dynamic GPU route shapes
required by the optimization plan:

- `test/05_perf/web_server_nginx_compare/external_compare_report.spl` adds a
  general `external_ready_unmeasured_row` contract.
- `test/05_perf/web_server_nginx_compare/external_compare_report_spec.spl`
  proves a ready dynamic GPU plaintext row has no measured RPS and cannot claim
  speedup.
- `scripts/check/check-web-server-nginx-compare-report.shs` now emits:
  - `dynamic_gpu_plaintext`:
    `native_simple_gpu_route_plaintext` vs `cpu_simple_plaintext`;
  - `dynamic_gpu_json`:
    `native_simple_gpu_route_json` vs `cpu_simple_json`.
- Both rows are `ready_unmeasured` on this host because `wrk` is installed; the
  report reason is `run-live-simple-cpu-gpu-route-wrk-wrapper`.
- Evidence refreshed:
  `simple check test/05_perf/web_server_nginx_compare/external_compare_report.spl test/05_perf/web_server_nginx_compare/external_compare_report_spec.spl`
  passes, and `sh scripts/check/check-web-server-nginx-compare-report.shs`
  prints `STATUS: PASS web server nginx comparison report`.

These rows complete the HTTP matrix shape for dynamic GPU routes. They are not
live CPU-vs-GPU route measurements and do not claim speedup.

## 2026-06-17 Dynamic GPU Route Live Wrapper Note

The dynamic GPU route lane now has a dedicated live-comparison wrapper instead
of only readiness rows:

- `scripts/check/check-web-server-dynamic-gpu-route-compare.shs` starts from the
  base web comparison report, then updates `dynamic_gpu_plaintext` and
  `dynamic_gpu_json`.
- If live URLs are provided through `DYNAMIC_GPU_PLAINTEXT_URL`,
  `DYNAMIC_CPU_PLAINTEXT_URL`, `DYNAMIC_GPU_JSON_URL`, and
  `DYNAMIC_CPU_JSON_URL`, the wrapper can run `wrk` against the configured CPU
  and GPU route endpoints.
- `--self-test-dynamic-route-parser` validates `wrk` output parsing, p99 unit
  conversion, throughput calculation, RPS ratio formatting, and
  `measured_with_failures` classification without requiring live servers.
- On this host those live dynamic route server URLs are not configured, so the
  generated report records `live-fixture-unavailable` with reason
  `dynamic-gpu-route-live-server-not-configured` for both dynamic rows.
- `scripts/check/check-web-server-nginx-compare-report.shs` preserves those
  explicit live-fixture rows instead of reverting them to `ready_unmeasured`.
- Evidence refreshed:
  `simple check test/05_perf/web_server_nginx_compare/external_compare_report.spl test/05_perf/web_server_nginx_compare/external_compare_report_spec.spl`
  passes,
  `sh scripts/check/check-web-server-dynamic-gpu-route-compare.shs --self-test-dynamic-route-parser`
  prints `STATUS: PASS dynamic route parser self-test`,
  `sh scripts/check/check-web-server-dynamic-gpu-route-compare.shs`
  prints `STATUS: PASS web server dynamic GPU route comparison report`, and the
  base comparison wrapper still prints
  `STATUS: PASS web server nginx comparison report`.

This closes the wrapper/reporting gap for live dynamic routes. It does not
measure route throughput until real CPU and GPU route server URLs are supplied.

## 2026-06-17 Benchmark Normalization Contract Note

The external HTTP comparison lane now records normalized benchmark inputs as
first-class contract/report evidence rather than only prose in the plan:

- `test/05_perf/web_server_nginx_compare/external_compare_report.spl` adds
  `ExternalBenchmarkNormalization`, `external_http_benchmark_normalization`,
  `external_benchmark_normalization_complete`, and markdown formatting for the
  normalization table.
- `test/05_perf/web_server_nginx_compare/external_compare_report_spec.spl`
  covers the payload, keep-alive, connection, thread, duration, logging, worker,
  and CPU-affinity policies.
- `scripts/check/check-web-server-nginx-compare-report.shs` and
  `scripts/check/check-web-server-dynamic-gpu-route-compare.shs` emit the same
  `Benchmark Normalization` section into both
  `doc/09_report/perf/web_server_nginx_compare_2026-06-17.md` and
  `doc/10_metrics/perf/web_server_nginx_compare.md`.
- Current normalized values are same bytes per compared workload, `wrk`
  keep-alive, 1 connection, 1 thread, 1 second, logging disabled for the measured
  hot path, and CPU affinity explicitly reported as not pinned on this host.
- Evidence refreshed:
  `SIMPLE_LIB=src:test/05_perf simple check test/05_perf/web_server_nginx_compare/external_compare_report.spl test/05_perf/web_server_nginx_compare/external_compare_report_spec.spl`
  passes, `sh scripts/check/check-web-server-nginx-compare-report.shs` prints
  `STATUS: PASS web server nginx comparison report`, and
  `sh scripts/check/check-web-server-dynamic-gpu-route-compare.shs` prints
  `STATUS: PASS web server dynamic GPU route comparison report`.

## 2026-06-17 Request Wire Copy Removal Note

The first hot-path optimization slice from the benchmark plan is implemented in
the production async reverse-proxy worker:

- `src/lib/nogc_async_mut/http_server/worker.spl` no longer calls
  `async_proxy_serialize_request` before deciding that a request body must be
  streamed. For chunked or oversized request bodies, the worker now builds only
  the streaming header wire plus the pending streamed fragment instead of first
  allocating a full buffered request wire that is immediately discarded.
- Non-streamed requests still use `async_proxy_serialize_request`, so public
  proxy request behavior and upstream wire semantics are unchanged.
- Evidence refreshed:
  `SIMPLE_LIB=src simple check src/lib/nogc_async_mut/http_server/worker.spl src/lib/nogc_async_mut/http_server/proxy.spl test/01_unit/lib/nogc_async_mut/http_server/async_reverse_proxy_spec.spl`
  passes, optimizer analysis was run on
  `src/lib/nogc_async_mut/http_server/worker.spl`, and
  `sh scripts/check/check-proxy-live-socket-benchmark.shs` prints
  `STATUS: PASS proxy live socket benchmark` after the edit.

## 2026-06-17 Worker Op Dispatch Reduction Note

The worker dispatch lane now has a focused reduction for proxy request-body
operation guards:

- `src/lib/nogc_async_mut/http_server/worker.spl` adds
  `worker_tracked_op_exists`, a shared predicate for checking whether the
  worker already tracks an operation kind for a client fd.
- `proxy_request_body_send_inflight`,
  `proxy_request_body_recv_inflight`, and
  `submit_proxy_request_body_send` now reuse the shared predicate instead of
  duplicating the same linear scan over `op_fds` and `op_kinds`.
- `test/01_unit/lib/nogc_async_mut/http_server/async_reverse_proxy_spec.spl`
  covers fd/kind matching and mismatched array truncation semantics for the
  shared helper.
- Evidence refreshed:
  `SIMPLE_LIB=src simple check src/lib/nogc_async_mut/http_server/worker.spl test/01_unit/lib/nogc_async_mut/http_server/async_reverse_proxy_spec.spl`
  passes,
  `SIMPLE_LIB=src simple test test/01_unit/lib/nogc_async_mut/http_server/async_reverse_proxy_spec.spl --mode=interpreter --clean`
  passes with 100 tests, optimizer analysis on
  `src/lib/nogc_async_mut/http_server/worker.spl` now reports 532 opportunities
  after this slice, `SIMPLE_LIB=src simple spipe-docgen test/01_unit/lib/nogc_async_mut/http_server/async_reverse_proxy_spec.spl --output doc/06_spec --no-index`
  completes with 0 stubs, and
  `sh scripts/check/check-proxy-live-socket-benchmark.shs` prints
  `STATUS: PASS proxy live socket benchmark`.

## 2026-06-17 Proxy Buffer Backpressure Append Note

The proxy buffer reuse/backpressure lane now has a focused policy-layer guard:

- `src/lib/nogc_async_mut/http_server/proxy.spl` adds
  `async_proxy_append_pending_client_data`, a shared helper that appends new
  downstream bytes to already-pending client data instead of overwriting unsent
  bytes.
- `async_proxy_prepare_client_chunk` now uses the helper for no-body response
  headers, fixed response body chunks, decoded chunked response body chunks, and
  initial header/body preparation.
- The worker normally pauses upstream reads while `pending_client_data` is not
  empty; this helper makes the policy layer safe if response preparation is
  called with existing pending bytes and keeps `async_proxy_pending_client_over_budget`
  as the enforcement point.
- `test/01_unit/lib/nogc_async_mut/http_server/async_reverse_proxy_spec.spl`
  covers preserving unsent downstream bytes, detecting the resulting
  backpressure budget violation, and preventing another upstream receive.
- Evidence refreshed:
  `SIMPLE_LIB=src simple check src/lib/nogc_async_mut/http_server/proxy.spl src/lib/nogc_async_mut/http_server/worker.spl test/01_unit/lib/nogc_async_mut/http_server/async_reverse_proxy_spec.spl`
  passes,
  `SIMPLE_LIB=src simple test test/01_unit/lib/nogc_async_mut/http_server/async_reverse_proxy_spec.spl --mode=interpreter --clean`
  passes with 101 tests, optimizer analysis on
  `src/lib/nogc_async_mut/http_server/proxy.spl` reports 551 opportunities,
  `SIMPLE_LIB=src simple spipe-docgen test/01_unit/lib/nogc_async_mut/http_server/async_reverse_proxy_spec.spl --output doc/06_spec --no-index`
  completes with 0 stubs, and
  `sh scripts/check/check-proxy-live-socket-benchmark.shs` prints
  `STATUS: PASS proxy live socket benchmark`.

## 2026-06-17 DB Batch Admission Policy Note

The DB batch admission lane now has first-class queue policy evidence:

- `src/lib/nogc_sync_mut/web_db_offload/queue.spl` adds
  `GpuWdbDbBatchAdmission`, `gpu_wdb_db_item_count`,
  `gpu_wdb_db_batch_bytes`, and `gpu_wdb_db_batch_admission`.
- The admission helper accepts only DB work kinds, normalizes row/document/vector
  item counts into batch bytes, delegates to the existing `gpu_wdb_submit_batch`
  queue decision path, and reports `dispatch-gpu`, `run-cpu-fallback`, or
  `reject` with the original decision reason.
- `src/lib/nogc_sync_mut/web_db_offload/__init__.spl` exports the admission
  type and helpers through `std.web_db_offload`.
- `test/05_perf/web_db_offload/gpu_web_db_offload_bench_spec.spl` adds
  `db_batch_admission_policy_contract`, covering a coarse accepted scan batch,
  a full-queue join/aggregate CPU fallback, and a tiny document-filter CPU
  fallback before dispatch.
- `scripts/check/check-gpu-web-db-offload-benchmark-report.shs` emits the
  admission row into
  `doc/09_report/perf/gpu_web_db_offload_benchmark_2026-06-16.md` and
  `doc/10_metrics/perf/gpu_web_db_offload_benchmark.md`.
- Evidence refreshed:
  `SIMPLE_LIB=src simple check src/lib/nogc_sync_mut/web_db_offload/queue.spl src/lib/nogc_sync_mut/web_db_offload/__init__.spl test/05_perf/web_db_offload/gpu_web_db_offload_bench_spec.spl`
  passes, optimizer analysis on `queue.spl` reports 5 low MIR opportunities,
  and `sh scripts/check/check-gpu-web-db-offload-benchmark-report.shs` prints
  `STATUS: PASS gpu web/db offload benchmark report` with 15 passing examples
  and 0 generated doc stubs. A direct `simple test` invocation outside the
  wrapper still lacks the runtime-queue extern bindings for older runtime queue
  examples; the wrapper remains the authoritative benchmark gate for this spec.

## 2026-06-17 GPU Transfer Amortization Policy Note

The GPU transfer amortization lane now has host-safe queue accounting evidence:

- `src/lib/nogc_sync_mut/web_db_offload/queue.spl` adds
  `GpuWdbTransferAmortization` and `gpu_wdb_transfer_amortization`.
- The helper compares naive per-call payload plus fixed transfer overhead
  against one coalesced batch transfer, rejects invalid, tiny, or oversized
  shapes, and reports saved transfer bytes without making a hardware speedup
  claim.
- `test/05_perf/web_db_offload/gpu_web_db_offload_bench_spec.spl` adds
  `gpu_transfer_amortization_policy_contract` for four logical 8x2048 web
  transform calls. The contract records 65536 payload bytes, 69632 naive
  transfer bytes, 66560 amortized transfer bytes, and 3072 saved fixed-overhead
  bytes.
- `scripts/check/check-gpu-web-db-offload-benchmark-report.shs` emits the row
  into the GPU Web/DB benchmark report and metrics table with
  `none-transfer-amortization-policy-contract`.
- Evidence refreshed:
  `SIMPLE_LIB=src simple check src/lib/nogc_sync_mut/web_db_offload/queue.spl src/lib/nogc_sync_mut/web_db_offload/__init__.spl test/05_perf/web_db_offload/gpu_web_db_offload_bench_spec.spl`
  passes, optimizer analysis on `queue.spl` reports 8 low MIR opportunities,
  and `sh scripts/check/check-gpu-web-db-offload-benchmark-report.shs` prints
  `STATUS: PASS gpu web/db offload benchmark report` with 16 passing examples
  and 0 generated doc stubs.

## 2026-06-17 External DB Baseline Status Row Note

The DB external-comparison lane now records unavailable standard DB baselines as
first-class report rows instead of only prose:

- `test/05_perf/web_db_offload/gpu_web_db_offload_bench_spec.spl` adds
  external DB baseline status helpers for ClickHouse ClickBench scans, DuckDB
  TPC-H join/aggregate, PostgreSQL TPC-H join/aggregate, and MongoDB/YCSB-style
  document filtering. The helpers cover both unavailable and ready-unmeasured
  states so installed tools do not remain stale unavailable rows.
- The rows use backend `external-db-baseline`, timing source
  `external-db-baseline-status`, and hardware claim
  `none-external-db-baseline-contract`.
- On this host, `duckdb`, `clickhouse`, `clickhouse-client`, `psql`,
  `pgbench`, `mongosh`, and `mongo` are unavailable, so the generated rows
  record `external-db-baseline-unavailable:*not-installed` reasons and make no
  speedup claim.
- `scripts/check/check-gpu-web-db-offload-benchmark-report.shs` now requires the
  four rows in both
  `doc/09_report/perf/gpu_web_db_offload_benchmark_2026-06-16.md` and
  `doc/10_metrics/perf/gpu_web_db_offload_benchmark.md`, and chooses
  `external-db-baseline-ready-unmeasured:*` when the matching external DB tool
  is installed.
- The report script also accepts optional measured external DB output through
  `GPU_WDB_EXTERNAL_DB_BASELINE_OUTPUT` lines shaped as
  `GPU_WDB_EXTERNAL_DB_MEASURED=name|dataset|target|time_us`. Only known
  ClickHouse, DuckDB, PostgreSQL, and MongoDB baseline names with matching
  datasets, matching targets, positive timing, timing source
  `external-db-baseline-driver`, and hardware claim
  `external-db-baseline-measured` are accepted as measured rows.
- `scripts/check/check-gpu-web-db-offload-external-db-baselines.shs` is now the
  producer for that measured-output contract. It emits measured lines only when
  it can run a real external DB command: `clickhouse local` or configured
  `clickhouse-client`, local `duckdb`, configured `psql`, or configured
  `mongosh`/`mongo`. Otherwise it exits cleanly with no measured output. Its
  `--self-test` mode verifies the timer and all four strict measured-line
  shapes without requiring external DB tools.
- The external DB producer now sources
  `build/perf/gpu_web_db_offload/external-fixtures.env` by default before
  probing URL-backed DB baselines, with `DB_FIXTURE_ENV_FILE` available as an
  override. This makes the readiness env-template handoff directly usable by
  ClickHouse client, PostgreSQL, and MongoDB measured producer paths.
- Normal producer runs now print `STATUS: PASS external DB baseline producer
  rows:N` when measured rows are emitted, or
  `STATUS: WARN tool-unavailable:external-db-baselines` when no external DB
  baseline is available. Non-measured status lines are ignored by the benchmark
  report parser.
- `scripts/check/check-gpu-web-db-offload-benchmark-report.shs` runs that
  producer automatically when `GPU_WDB_EXTERNAL_DB_BASELINE_OUTPUT` was not
  supplied, then validates any emitted rows through the strict report contract.
- Evidence refreshed:
  `SIMPLE_LIB=src simple check test/05_perf/web_db_offload/gpu_web_db_offload_bench_spec.spl`
  passes, `sh -n scripts/check/check-gpu-web-db-offload-benchmark-report.shs`
  and `sh -n scripts/check/check-gpu-web-db-offload-external-db-baselines.shs`
  pass,
  `sh scripts/check/check-gpu-web-db-offload-external-db-baselines.shs --self-test`
  prints `STATUS: PASS external DB baseline producer self-test`,
  `sh scripts/check/check-gpu-web-db-offload-external-db-baselines.shs --self-test-env-file-source`
  prints `STATUS: PASS external DB baseline env-file source self-test`,
  `sh scripts/check/check-gpu-web-db-offload-external-db-baselines.shs --self-test-no-rows-status`
  prints `STATUS: PASS external DB baseline no-row status self-test`,
  `scripts/check/check-gpu-web-db-offload-external-db-baselines.shs` prints
  `STATUS: WARN tool-unavailable:external-db-baselines` on this host,
  `sh scripts/check/check-gpu-web-db-offload-benchmark-report.shs --self-test-external-db-measured-parser`
  prints `STATUS: PASS external DB measured parser self-test`, and
  `sh scripts/check/check-gpu-web-db-offload-benchmark-report.shs` prints
  `STATUS: PASS gpu web/db offload benchmark report` with 18 passing examples
  and 0 generated doc stubs.

## 2026-06-17 Benchmark Environment Reporting Note

The benchmark report wrappers now record host environment context required by
the optimization plan:

- `scripts/check/check-web-server-nginx-compare-report.shs`,
  `scripts/check/check-web-server-nginx-live-compare.shs`, and
  `scripts/check/check-gpu-web-db-offload-benchmark-report.shs` add environment
  sections with CPU model, core count, kernel, RAM, storage, CUDA/nvidia-smi
  visibility, and Simple runtime path.
- `doc/09_report/perf/web_server_nginx_compare_2026-06-17.md` now records:
  AMD Ryzen Threadripper 1950X, 32 cores, Linux `6.8.0-117-generic`, RAM,
  storage, two visible NVIDIA GPUs, and `auto:/home/ormastes/.local/bin/simple`.
- `doc/09_report/perf/gpu_web_db_offload_benchmark_2026-06-16.md` records the
  same host details plus `CUDA_VISIBLE_DEVICES=unset`.
- Evidence refreshed:
  `sh scripts/check/check-web-server-nginx-compare-report.shs` prints
  `STATUS: PASS web server nginx comparison report`, and
  `sh scripts/check/check-gpu-web-db-offload-benchmark-report.shs` prints
  `STATUS: PASS gpu web/db offload benchmark report`.

## 2026-06-17 DB Standard-Shape Benchmark Row Note

The GPU Web/DB benchmark now maps Simple DB offload targets to standard
benchmark families before any external DB speedup claim:

- `test/05_perf/web_db_offload/gpu_web_db_offload_bench_spec.spl` adds
  host-safe rows for:
  - `db_clickbench_olap_scan_shape_contract`;
  - `db_tpch_join_aggregate_shape_contract`;
  - `db_benchbase_ycsb_document_shape_contract`;
  - `db_ann_vector_search_shape_contract`.
- These rows use the existing DB dispatch targets
  `gpu_db_columnar_scan_batch`, `gpu_db_join_aggregate_batch`,
  `gpu_db_document_filter_batch`, and `gpu_db_vector_search_batch`, but mark
  the backend as `host-safe-standard-shape` and record unavailable standard
  baselines in `fallback_reason`.
- `scripts/check/check-gpu-web-db-offload-benchmark-report.shs` now requires
  those rows in `doc/09_report/perf/gpu_web_db_offload_benchmark_2026-06-16.md`
  and `doc/10_metrics/perf/gpu_web_db_offload_benchmark.md`.
- Evidence refreshed:
  `simple check test/05_perf/web_db_offload/gpu_web_db_offload_bench_spec.spl`
  passes, and `sh scripts/check/check-gpu-web-db-offload-benchmark-report.shs`
  prints `STATUS: PASS gpu web/db offload benchmark report`.

These rows preserve the ClickBench/TPC-H/BenchBase/YCSB/ANN workload matrix.
They are not external DB measurements and do not claim GPU or Simple speedup.

## 2026-06-17 Optimization Benchmark Plan Note

The external-comparison optimization plan is now documented at
`doc/03_plan/perf/gpu_web_db_offload_optimization_benchmark_plan.md`.
It keeps the lane status as implementation in progress and defines the required
Simple-vs-external benchmark matrix before any production speedup claim:
NGINX, HAProxy, Envoy, Caddy/H2O/uWebSockets-style HTTP baselines where
available; TechEmpower/wrk-shaped HTTP workloads; and ClickBench, TPC-H,
BenchBase/YCSB-style DB workload shapes. Current CUDA and proxy evidence remains
contract/reliability evidence until those reproducible comparison rows exist.

## 2026-06-16 Current Reverse-Proxy Upload Note

The reliable CPU reverse-proxy upload streaming gate is now green for the native
HttpServer fixture. This cycle fixed reusable async driver op-id returns by
making every `submit_* -> i64` return explicit, hardened the upload harness
cleanup/strace path, replaced native-unsupported proxy `Dict.remove(...)`
cleanup with native-safe map rebuilding, removed the unsafe accept-op scalar
fallback that treated response byte counts as accepted fds, kept upstream
response reads on tracked `OP_PROXY_RECV_RESPONSE` ownership, and moved worker
chunked request-body handling to raw pass-through with bounded pending bytes and
terminal-chunk detection. Focused checks pass, the native upload fixture
rebuilds, and `SIMPLE_PROXY_UPLOAD_SKIP_BUILD=1
sh scripts/check/check-proxy-live-httpserver-upload.shs` prints
`STATUS: PASS proxy live HttpServer upload streaming`. See
`doc/08_tracking/bug/httpserver_reverse_proxy_live_no_response_2026-06-16.md`
for the bug evidence trail. Next reverse-proxy work should move to broader
production hardening: timeout/backpressure coverage, connection pool stress,
and throughput evidence before expanding GPU performance work.

## 2026-06-16 Current Reverse-Proxy Pool Note

The native HttpServer upstream pool reuse gate is green again after the upload
streaming changes. The worker fast response path now carries HTTP/1.1
keep-alive reuse eligibility onto the proxy connection before
`OP_PROXY_SEND_CLIENT` completes, so framed backend responses can release their
upstream fd back to `proxy_upstream_pool`. The pool evidence wrapper now drains
the proxied client response until close before sending the second request,
avoiding a race with the worker send-completion release callback. Focused
checks pass and `sh scripts/check/check-proxy-live-httpserver-pool.shs` prints
`STATUS: PASS proxy live HttpServer upstream pool reuse`.

## 2026-06-16 Current Reverse-Proxy Tunnel Note

The native HttpServer Upgrade/WebSocket tunnel gate is green for the live
fixture. The worker now forwards the backend `101 Switching Protocols` response
to the client, relays a binary client payload with a leading NUL byte to the
backend, and relays the backend echo back to the client. The fix keeps HTTP
control-plane validation on CPU, uses a conservative text fast path for native
`101` validation, stores binary driver sends in native-safe sidecar arrays, and
assigns post-handshake tunnel byte buffers directly in the worker hot path.
Focused checks pass and the native fixture gate passes with:

```text
SIMPLE_LIB=src bin/simple native-build --clean --no-incremental --source src/lib --source test/05_perf/web --entry test/05_perf/web/proxy_live_httpserver_proxy.spl --entry-closure --strip --output build/perf/proxy_live_httpserver_tunnel/proxy_live_httpserver_proxy
PROXY_LIVE_SKIP_BUILD=1 sh scripts/check/check-proxy-live-httpserver-tunnel.shs
STATUS: PASS proxy live HttpServer upgrade tunnel
```

## 2026-06-16 Current Reliable Proxy Suite Note

The reliability-first CPU proxy gates now have a single aggregate wrapper:

```text
sh scripts/check/check-proxy-live-httpserver-reliable-suite.shs
STATUS: PASS proxy live HttpServer reliable suite
```

This wrapper runs live static serving, live reverse proxy, live upstream pool
reuse, live upload streaming, and live Upgrade/WebSocket tunnel evidence before
GPU performance claims are refreshed. Native builds still report the known
non-critical skips for `h2_hpack.spl` and
`security/auth/context_propagation.spl`, but every live fixture in the suite
reaches its `STATUS: PASS` line.

## 2026-06-16 Current GPU Web/DB Device Evidence Note

The GPU web/DB native-device evidence is current on this host. The native probe
reports `measured | cuda | cuda-device-0 | gpu_db_vector_search_batch` with
`kernel_time_us=149`, `completion_latency_us=149`, `gpu_hits=1`, and hardware
claim `native-device-measured`. The benchmark report gate also passes and
records measured CUDA contract rows for `db_vector_cuda_measured`
(`device_time_us=264`) and `db_columnar_scan_cuda_measured`
(`device_time_us=210`), plus the CPU-oracle-gated
`web_inference_device_validated_contract` and the tiny-batch CPU fallback row.
This proves real CUDA kernel execution for the reusable vector and columnar DB
contract shapes, while still keeping broad production DB/web operator
throughput marked as remaining work.

The benchmark report gate now also runs
`test/05_perf/web_db_offload/gpu_web_db_offload_join_aggregate_cuda_measured_driver.spl`
and records `db_join_aggregate_cuda_measured` only when the CUDA oracle passes
for the `gpu_db_join_aggregate_batch` target and
`pure_sql_join_aggregate_group_count` dataset. The latest local metrics table
records this row with `device_time_us=196` and hardware claim
`native-device-measured`, extending measured CUDA DB contract evidence from
vector and columnar scan to join/aggregate batches.

The same benchmark gate now runs
`test/05_perf/web_db_offload/gpu_web_db_offload_document_filter_cuda_measured_driver.spl`
and records `db_document_filter_cuda_measured` only when the CUDA oracle passes
for `gpu_db_document_filter_batch` and the `nosql_document_filter_metadata`
dataset. The latest local metrics table records this row with
`device_time_us=161` and hardware claim `native-device-measured`, extending
measured CUDA DB contract evidence to the NoSQL document-filter target used by
RAM and SSD document collection offload facades.

The benchmark report gate now also runs
`test/05_perf/web_db_offload/gpu_web_db_offload_web_transform_cuda_measured_driver.spl`
and records `web_transform_cuda_measured` only when the CUDA oracle passes for
`gpu_web_transform_batch` and the `web_transform_8x2048_response_match`
dataset. The latest local metrics table records this row with
`device_time_us=182` and hardware claim `native-device-measured`, extending
measured CUDA web contract evidence beyond inference to the transform route
shape.

The benchmark report gate now also runs
`test/05_perf/web_db_offload/gpu_web_db_offload_web_embedding_cuda_measured_driver.spl`
and
`test/05_perf/web_db_offload/gpu_web_db_offload_web_rank_cuda_measured_driver.spl`.
It records `web_embedding_cuda_measured` only for `gpu_web_embedding_batch` on
`web_embedding_16x512_response_match`, and `web_rank_cuda_measured` only for
`gpu_web_rank_batch` on `web_rank_32x256_response_match`. The latest local
metrics table records these rows with `device_time_us=208` and
`device_time_us=211`, respectively, both with hardware claim
`native-device-measured`.

The RAM NoSQL document-filter replacement gate now reaches the storage facade
and reusable DB profile layer. `db_storage_execute_documents_with_device_backend_validated`
and `db_offload_profile_execute_documents_device` both keep CPU document IDs
authoritative unless the native backend has measured production device evidence
and GPU candidate document IDs match the CPU oracle. Focused storage/profile
specs pass with match and mismatch coverage.

Verification refresh: `sh scripts/check/check-gpu-web-db-offload-native-device-probe.shs`
and `sh scripts/check/check-gpu-web-db-offload-benchmark-report.shs` both print
`STATUS: PASS` on this host. The broader benchmark gate checks nine perf driver
files and keeps measured CUDA rows behind CPU-oracle validation; the native
probe gate checks three files and accepts measured hardware claims only for
positive GPU device timings.

## 2026-06-16 Pure SQL Production Join/Aggregate Note

Pure SQL now exposes an explicit production-device validation boundary for
join/aggregate SELECTs through
`PureDatabase.query_join_aggregate_with_device_backend_validated(...)`. Unlike
the scan/filter/project device path, this API requires both GPU candidate row
IDs and GPU candidate SQL rows, then delegates to the reusable
`sql_join_aggregate_offload_execute_device_validated(...)` facade. CPU rows
remain authoritative unless the backend has a production device claim, row IDs
match, and full SQL result rows match. The focused Pure SQL offload spec covers
production replacement and SQL-row mismatch fallback, and
`bin/simple test test/01_unit/lib/nogc_sync_mut/database/pure_sql_offload_spec.spl
--mode=interpreter` passes with 16 scenarios.

## Implemented Slice

- `src/lib/nogc_sync_mut/web_db_offload/contract.spl`
- `src/lib/nogc_sync_mut/web_db_offload/__init__.spl`
- `test/01_unit/lib/nogc_sync_mut/web_db_offload/gpu_web_db_offload_contract_spec.spl`
- `test/03_system/lib/web_db_offload/feature/gpu_web_db_offload_spec.spl`
- `doc/06_spec/test/01_unit/lib/nogc_sync_mut/web_db_offload/gpu_web_db_offload_contract_spec.md`
- `doc/06_spec/test/03_system/lib/web_db_offload/feature/gpu_web_db_offload_spec.md`
- `src/lib/nogc_sync_mut/database/vector/offload_plan.spl`
- `test/01_unit/lib/nogc_sync_mut/database/vector/vector_offload_plan_spec.spl`
- `doc/06_spec/test/01_unit/lib/nogc_sync_mut/database/vector/vector_offload_plan_spec.md`
- `src/lib/nogc_sync_mut/database/gpu_mode_plan.spl`
- `test/01_unit/lib/nogc_sync_mut/database/gpu_mode_plan_spec.spl`
- `doc/06_spec/test/01_unit/lib/nogc_sync_mut/database/gpu_mode_plan_spec.md`
- `src/lib/nogc_sync_mut/http_server/proxy.spl`
- `test/01_unit/lib/nogc_sync_mut/http_server/reverse_proxy_spec.spl`
- `doc/06_spec/test/01_unit/lib/nogc_sync_mut/http_server/reverse_proxy_spec.md`
- `src/lib/nogc_async_mut/http_server/proxy.spl`
- `src/lib/nogc_async_mut/http_server/worker.spl`
- `src/lib/nogc_async_mut/io/driver.spl`
- `test/01_unit/lib/nogc_async_mut/http_server/async_reverse_proxy_spec.spl`
- `doc/06_spec/test/01_unit/lib/nogc_async_mut/http_server/async_reverse_proxy_spec.md`
- `src/lib/nogc_sync_mut/web_db_offload/queue.spl`
- `src/lib/nogc_sync_mut/web_db_offload/library.spl`
- `src/lib/nogc_sync_mut/web_db_offload/device_backend.spl`
- `src/lib/nogc_sync_mut/web_db_offload/scheduler.spl`
- `src/lib/nogc_sync_mut/web_db_offload/web_route.spl`
- `test/01_unit/lib/nogc_sync_mut/web_db_offload/gpu_web_db_offload_library_spec.spl`
- `doc/06_spec/test/01_unit/lib/nogc_sync_mut/web_db_offload/gpu_web_db_offload_library_spec.md`
- `test/01_unit/lib/nogc_sync_mut/web_db_offload/gpu_web_db_offload_device_backend_spec.spl`
- `doc/06_spec/test/01_unit/lib/nogc_sync_mut/web_db_offload/gpu_web_db_offload_device_backend_spec.md`
- `test/01_unit/lib/nogc_sync_mut/web_db_offload/gpu_web_db_offload_scheduler_spec.spl`
- `doc/06_spec/test/01_unit/lib/nogc_sync_mut/web_db_offload/gpu_web_db_offload_scheduler_spec.md`
- `test/01_unit/lib/nogc_sync_mut/web_db_offload/web_route_gpu_offload_spec.spl`
- `doc/06_spec/test/01_unit/lib/nogc_sync_mut/web_db_offload/web_route_gpu_offload_spec.md`
- `src/lib/nogc_sync_mut/web_db_offload/web_profile.spl`
- `test/01_unit/lib/nogc_sync_mut/web_db_offload/web_route_profile_spec.spl`
- `doc/06_spec/test/01_unit/lib/nogc_sync_mut/web_db_offload/web_route_profile_spec.md`
- `src/lib/nogc_sync_mut/database/db_offload.spl`
- `test/01_unit/lib/nogc_sync_mut/database/db_gpu_batch_offload_spec.spl`
- `doc/06_spec/test/01_unit/lib/nogc_sync_mut/database/db_gpu_batch_offload_spec.md`
- `src/lib/nogc_sync_mut/database/storage_mode_offload.spl`
- `test/01_unit/lib/nogc_sync_mut/database/storage_mode_offload_spec.spl`
- `doc/06_spec/test/01_unit/lib/nogc_sync_mut/database/storage_mode_offload_spec.md`
- `src/lib/nogc_sync_mut/database/query_offload.spl`
- `test/01_unit/lib/nogc_sync_mut/database/db_query_offload_spec.spl`
- `doc/06_spec/test/01_unit/lib/nogc_sync_mut/database/db_query_offload_spec.md`
- `src/lib/nogc_sync_mut/database/query.spl`
- `src/lib/nogc_sync_mut/database/wal.spl`
- `src/lib/nogc_sync_mut/database/core.spl`
- `test/01_unit/lib/nogc_sync_mut/database/query_builder_offload_spec.spl`
- `doc/06_spec/test/01_unit/lib/nogc_sync_mut/database/query_builder_offload_spec.md`
- `src/lib/nogc_sync_mut/database/offload_profile.spl`
- `test/01_unit/lib/nogc_sync_mut/database/db_offload_profile_spec.spl`
- `doc/06_spec/test/01_unit/lib/nogc_sync_mut/database/db_offload_profile_spec.md`
- `src/lib/nogc_sync_mut/database/nosql_offload.spl`
- `test/01_unit/lib/nogc_sync_mut/database/nosql_document_offload_spec.spl`
- `doc/06_spec/test/01_unit/lib/nogc_sync_mut/database/nosql_document_offload_spec.md`
- `src/lib/nogc_sync_mut/database/vector/search_offload.spl`
- `test/01_unit/lib/nogc_sync_mut/database/vector/vector_search_offload_adapter_spec.spl`
- `doc/06_spec/test/01_unit/lib/nogc_sync_mut/database/vector/vector_search_offload_adapter_spec.md`
- `src/lib/nogc_sync_mut/web_framework/gpu_offload.spl`
- `test/01_unit/lib/nogc_sync_mut/web_framework/gpu_offload_spec.spl`
- `doc/06_spec/test/01_unit/lib/nogc_sync_mut/web_framework/gpu_offload_spec.md`
- `src/lib/nogc_async_mut/web_framework/dispatcher.spl`
- `src/lib/nogc_async_mut/web_framework/app.spl`
- `test/01_unit/lib/nogc_async_mut/web_framework/dispatcher_spec.spl`
- `doc/06_spec/test/01_unit/lib/nogc_async_mut/web_framework/dispatcher_spec.md`
- `test/05_perf/web_db_offload/gpu_web_db_offload_bench_spec.spl`
- `doc/06_spec/test/05_perf/web_db_offload/gpu_web_db_offload_bench_spec.md`
- `test/05_perf/web_db_offload/gpu_web_db_offload_native_device_probe_spec.spl`
- `test/05_perf/web_db_offload/gpu_web_db_offload_native_device_probe_driver.spl`
- `test/05_perf/web_db_offload/gpu_web_db_offload_cuda_measured_driver.spl`
- `test/05_perf/web_db_offload/gpu_web_db_offload_columnar_scan_cuda_measured_driver.spl`
- `test/05_perf/web_db_offload/gpu_web_db_offload_join_aggregate_cuda_measured_driver.spl`
- `test/05_perf/web_db_offload/gpu_web_db_offload_document_filter_cuda_measured_driver.spl`
- `test/05_perf/web_db_offload/gpu_web_db_offload_web_inference_cuda_measured_driver.spl`
- `test/05_perf/web_db_offload/gpu_web_db_offload_web_embedding_cuda_measured_driver.spl`
- `test/05_perf/web_db_offload/gpu_web_db_offload_web_rank_cuda_measured_driver.spl`
- `test/05_perf/web_db_offload/gpu_web_db_offload_web_transform_cuda_measured_driver.spl`
- `doc/06_spec/test/05_perf/web_db_offload/gpu_web_db_offload_native_device_probe_spec.md`
- `scripts/check/check-gpu-web-db-offload-benchmark-report.shs`
- `scripts/check/check-gpu-web-db-offload-native-device-probe.shs`
- `doc/09_report/perf/gpu_web_db_offload_benchmark_2026-06-16.md`
- `doc/10_metrics/perf/gpu_web_db_offload_benchmark.md`
- `doc/09_report/perf/gpu_web_db_offload_native_device_probe_2026-06-16.md`
- `doc/10_metrics/perf/gpu_web_db_offload_native_device_probe.md`
- `src/compiler_rust/runtime/src/host_gpu_lane.rs`
- `src/runtime/runtime_native.c`
- `src/compiler_rust/common/src/runtime_symbols.rs`
- `src/compiler_rust/compiler/src/interpreter_eval.rs`
- `src/compiler_rust/compiler/src/codegen/runtime_sffi.rs`
- `src/compiler_rust/compiler/src/interpreter_extern/host_gpu_lane.rs`
- `src/compiler_rust/compiler/src/interpreter_extern/mod.rs`
- `src/compiler_rust/compiler/src/interpreter_sffi.rs`
- `src/compiler_rust/compiler/src/elf_utils.rs`
- `test/05_perf/db/db_bench_driver.spl`
- `scripts/check/check-db-benchmark-report.shs`
- `doc/09_report/perf/perf_baseline_db_2026-06-13.md`
- `doc/10_metrics/perf/perf_baseline_db_table.md`
- `test/05_perf/web/proxy_reverse_proxy_bench_spec.spl`
- `test/05_perf/web/proxy_live_native_backend.spl`
- `test/05_perf/web/proxy_live_native_cached_proxy.spl`
- `test/05_perf/web/proxy_live_httpserver_proxy.spl`
- `scripts/check/check-proxy-benchmark-report.shs`
- `scripts/check/check-proxy-live-socket-benchmark.shs`
- `scripts/check/check-proxy-live-httpserver.shs`
- `doc/06_spec/test/05_perf/web/proxy_reverse_proxy_bench_spec.md`
- `src/lib/nogc_sync_mut/db/dbfs_engine/offload_snapshot.spl`
- `test/02_integration/storage/dbfs/dbfs_ssd_offload_snapshot_spec.spl`
- `doc/06_spec/test/02_integration/storage/dbfs/dbfs_ssd_offload_snapshot_spec.md`

This slice implements the reliability-first offload decision contract:

- CPU fallback is required before GPU dispatch.
- HTTP/proxy control-plane work remains CPU fallback.
- stale DB generations fall back instead of using GPU results.
- full queues and tiny batches fall back.
- invalid budgets, empty batches, and negative queue depths reject before dispatch.
- GPU evidence is reported only for eligible coarse batches.
- reusable runtime snapshots build web/DB requests through one API.
- reusable execution plans choose GPU library batch targets only after admission.
- reusable queue reservations reserve a single GPU slot for eligible batches.
- reusable batch windows compute average item size and release the queue slot when
  the batch falls back to CPU.
- RAM, SSD, and NoSQL/vector mode gates reject unsafe batches.

The DB vector slice adds a planner-only adapter:

- estimates vector search batch bytes from candidate count and dimensions.
- delegates queue/batch decisions to `std.web_db_offload.contract`.
- plans eligible coarse vector batches for `gpu_db_vector_search_batch`.
- keeps small batches and unavailable GPU runtime on CPU fallback.
- rejects NoSQL-style metadata filtering unless metadata remains CPU-owned.

The general DB GPU mode slice adds a public planner facade:

- `DbGpuMode.RamOnly` plans scan/filter/project batches through the shared GPU
  batch policy.
- `DbGpuMode.SsdAccelerated` requires a current WAL generation and falls back on
  stale generation evidence.
- `DbGpuMode.NoSqlDocument` rejects GPU-owned metadata filtering so metadata
  remains CPU authoritative.
- `DbGpuMode.VectorSearch` reuses the vector-search GPU target and queue
  accounting.

The reusable DB adapter slice adds registry-gated execution boundaries:

- `db_gpu_batch_offload_execute` submits RAM-only and SSD-accelerated
  scan/filter/project or join/aggregate batches through the shared queue.
- GPU use is reported only when `gpu_db_columnar_scan_batch` or
  `gpu_db_join_aggregate_batch` is registered in the shared GPU library
  registry.
- `db_gpu_batch_offload_execute_device_for_generation` runs RAM/SSD DB batches
  through `GpuWdbDeviceBackend` and returns strict device evidence beside the
  CPU-authoritative `DbGpuBatchOffloadExecution`.
- SSD-accelerated batches require current WAL generation evidence before GPU
  dispatch.
- CPU row IDs remain authoritative regardless of whether GPU accounting accepts
  a batch.
- `nosql_document_offload_execute` submits coarse document-filter batches while
  rejecting GPU-owned metadata filtering.
- `vector_search_offload_execute` wires vector search planning to the shared
  queue and library registry while keeping CPU search results authoritative.
- `vector_search_offload_execute_device_validated` adds strict measured-native
  replacement for vector result IDs: production device timing and CPU-oracle ID
  agreement are both required before GPU candidate `SearchResult` values replace
  CPU-authoritative results.

The strict device-backend runner slice moves native hardware evidence below the
shared queue instead of leaving it only in perf scripts:

- `GpuWdbDeviceBackend` records backend name, generation, registered targets,
  native execution capability, and device name.
- `gpu_wdb_device_backend_registry` exposes targets only when the backend can
  execute native device work, so host-safe mocks cannot claim production GPU
  execution.
- `gpu_wdb_run_device_batch` combines current-generation target registration,
  shared queue admission, and measured device timing into one
  `GpuWdbDeviceRunResult`.
- `production_device_claim` is true only for an accepted native backend with
  positive measured device time; stale generations and perf-only/mock backends
  fall back before a production device claim can be recorded.

The vector store search slice moves vector search batching below the facade
boundary:

- `VectorSearchAccumulatedOffloadExecution` carries CPU-authoritative vector
  search results alongside an accumulated DB query offload record.
- `VectorDatabase.search_with_offload_accumulating` runs normal CPU vector
  search first, then defers small background vector batches through
  `GpuWdbWorkKind.DbVectorSearch` when scheduler policy says to accumulate.
- `VectorDatabase.search_with_filter_offload_accumulating` keeps metadata
  filtering CPU-owned before producing vector offload accounting.
- direct vector-store offload and accumulated vector-store offload both preserve
  CPU result order and IDs as authoritative output.
- `VectorDatabase.search_with_device_backend_validated` exposes the measured
  native vector replacement gate at the live vector-store boundary while still
  deriving the CPU oracle from ordinary `search`.

The NoSQL RAM document collection slice moves document filtering below the
facade boundary:

- `NoSqlDocumentRecord` and `NoSqlDocumentCollection` provide a small
  RAM-backed document collection with encoded-size and metadata state.
- `NoSqlDocumentCollection.to_text`, `from_text`, `save`, and `load` provide a
  durable text-backed collection format for metadata-filter state, using the
  existing runtime write-at-offset file primitive.
- `NoSqlDocumentCollection.filter_metadata_ids` performs CPU-owned metadata
  filtering and returns authoritative document IDs.
- `NoSqlDocumentCollection.filter_metadata_with_offload` feeds the
  CPU-filtered IDs, collection size, average encoded bytes, and generation
  freshness into `nosql_document_offload_execute`.
- stale collection generations fall back through the existing CPU path before
  document-filter GPU accounting can be reported.
- reloaded durable collections can feed the same CPU-authoritative metadata IDs
  into document-filter GPU accounting.
- `nosql_document_offload_execute_device_validated` adds the RAM document
  measured-native replacement gate below the collection facade: production
  device timing and CPU/GPU document-ID agreement are required before GPU
  candidates replace CPU-authoritative metadata-filter IDs.

The RAM table storage batch slice moves row batch materialization below the
query facade boundary:

- `SdnTable.valid_row_ids` derives CPU-authoritative row indexes from storage
  state and excludes soft-deleted `valid=false` rows.
- `SdnTable.storage_row_batch_with_offload` feeds valid row count, valid row
  IDs, and average row byte evidence into the RAM-only storage-mode adapter.
- `SdnTable.storage_row_batch_with_mode_offload` adds the same storage-owned row
  manifest for explicit RAM/SSD modes and carries WAL generation freshness into
  SSD-accelerated table batches.
- `DbStorageDeviceOffloadExecution` and
  `db_storage_execute_rows_with_device_backend` bridge storage-mode row batches
  through the strict native device-backend runner while preserving the existing
  CPU-authoritative storage execution shape.
- `SdnTable.storage_row_batch_with_device_backend` and
  `storage_row_batch_with_mode_device_backend` expose the native device-backed
  path directly from table storage, using the same `valid_rows().len()` and
  `valid_row_ids()` manifest as the registry-backed helper.
- eligible coarse RAM table batches can report `gpu_db_columnar_scan_batch`
  evidence, fresh SSD table batches can use the same target, and stale SSD,
  tiny, or unregistered batches stay CPU fallback.

The reusable scheduler slice adds shared web/DB admission policy:

- `GpuWdbScheduleRequest` captures work kind, batch size, item count,
  scheduling class, defer policy, and runtime snapshot before queue mutation.
- `gpu_wdb_schedule_registered` dispatches to GPU only when the executable
  target is registered and the shared reliability budget admits the batch.
- small batch/background work can be deferred to a later accumulator instead of
  forcing tiny GPU kernels.
- interactive small work falls back to CPU for latency and reliability.
- missing CPU fallback, invalid batches, and unsupported control-plane work fail
  closed or remain CPU-owned.
- `GpuWdbBatchAccumulator` stores homogeneous deferred work kind, total bytes,
  item count, pending request count, and closed state.
- accumulator add/flush/reset helpers combine tiny background or batch work into
  a non-deferred scheduler request once the accumulated bytes reach the GPU
  minimum batch size.
- `gpu_wdb_batch_accumulator_flush_registered` submits a ready accumulator
  through the registered GPU library and shared queue, then resets state only
  when GPU dispatch or CPU fallback has handled the accumulated work.
- hard-rejected accumulator flushes retain their pending state so callers can
  report or retry after restoring required runtime evidence.
- accumulator additions reject mixed work kinds, invalid zero-sized batches, and
  control-plane/proxy work so CPU ownership remains reliable.

The DB storage-mode facade slice adds a DB-server-facing mode dispatcher:

- `db_storage_execute_rows` routes RAM-only and SSD-accelerated
  scan/filter/project or join/aggregate work through the row batch adapter.
- `db_storage_execute_documents` routes NoSQL document filters through the
  document adapter while preserving CPU-owned metadata filtering.
- `db_storage_execute_vector` routes vector search through the vector adapter
  and exposes CPU result IDs as authoritative output.
- `DbStorageOffloadExecution` gives DB server code a single result shape with
  dispatch target, reason, GPU-use flag, CPU-authoritative flag, and result IDs.
- `db_storage_execute_rows_with_device_backend_validated` is the first
  replacement gate: it requires a strict native `GpuWdbDeviceBackend`
  production claim and matching GPU candidate row IDs before scan/filter/project
  rows stop being CPU-authoritative. Perf-only backends and mismatched GPU row
  candidates retain CPU authority and fall back.
- `db_storage_execute_documents_with_device_backend_validated` applies the same
  measured-native replacement policy to RAM NoSQL document-filter batches,
  replacing CPU-owned document IDs only after production device timing and
  CPU/GPU candidate agreement.

The DB query offload facade slice adds one DB-server-facing query entrypoint:

- `DbQueryOffloadRequest` captures row, document, and vector query offload
  metadata in a single request shape.
- `db_query_rows`, `db_query_documents`, and `db_query_vector` build typed
  requests for RAM-only, SSD-accelerated, NoSQL, and vector modes.
- `db_query_offload_execute` dispatches to the correct storage-mode adapter
  while preserving CPU-authoritative row, document, and vector IDs.
- `db_query_offload_execute_scheduled` runs shared scheduler admission before
  DB query queue mutation so tiny batch/background document, row, or vector work
  can defer to the batch accumulator instead of launching inefficient GPU work.
- `db_query_offload_execute_accumulating` adds deferred DB query work to
  `GpuWdbBatchAccumulator` while preserving CPU-authoritative row, document, and
  vector result IDs.
- join/aggregate query requests now participate in the same accumulator path,
  so small SQL aggregate batches can defer into `GpuWdbWorkKind.DbJoinAggregate`
  instead of forcing tiny GPU kernels.
- `db_query_offload_execute_for_ssd_snapshot` lets DB server code route
  DBFS-owned SSD freshness evidence through the query facade for
  scan/filter/project and join/aggregate row work.
- document and vector workloads are rejected on the SSD snapshot query path with
  `query-mode-workload-mismatch`, keeping row snapshots out of non-row
  workloads.
- GPU-worthy DB query batches bypass the accumulator and dispatch through the
  existing storage-mode adapters; non-deferred queries return
  `query-not-deferred` with unchanged accumulator state.
- invalid mode/workload pairs fall back with `query-mode-workload-mismatch`
  instead of emitting misleading GPU evidence.
- `db_query_offload_execute_rows_device_validated` exposes the strict native
  row replacement gate at the DB query facade. It keeps query rows
  CPU-authoritative for perf-only backends and mismatched GPU candidate row IDs,
  and only marks scan/filter/project row output non-CPU-authoritative after a
  production `GpuWdbDeviceBackend` claim and CPU-oracle row-ID agreement.

The QueryBuilder aggregate offload slice narrows the row-operator integration
gap:

- `QueryBuilderAggregateOffloadExecution` carries CPU-authoritative aggregate
  count results alongside storage-mode offload accounting.
- `QueryBuilder.count_with_storage_offload` and
  `query_builder_count_with_storage_offload` route aggregate counts through
  `DbStorageOffloadWorkload.JoinAggregate` while preserving CPU-computed row
  IDs as authoritative evidence.
- `QueryBuilder.count_with_storage_offload_accumulating` and
  `query_builder_count_with_storage_offload_accumulating` expose the
  accumulator-aware aggregate path for DB server code; the implementation
  delegates to `db_query_offload_execute_accumulating` with
  `GpuWdbWorkKind.DbJoinAggregate`.
- `query_builder_offload_spec` now covers RAM-only scan/filter/project and
  aggregate-count join/aggregate accounting through executable SSpec evidence.
- the executable QueryBuilder spec uses the stable storage facade for direct
  join/aggregate accounting because the interpreter remains fragile around
  newly added QueryBuilder wrapper calls, while `db_query_offload_spec` covers
  the accumulator semantics at the stable query-facade layer.

The QueryBuilder measured-native row slice adds the first live QueryBuilder
replacement gate:

- `QueryBuilderDeviceOffloadExecution` carries CPU-produced rows beside the
  validated native-device storage execution.
- `QueryBuilder.execute_with_device_backend_validated` and
  `query_builder_execute_with_device_backend_validated` run RAM-only
  scan/filter/project row IDs through the query-facade production replacement
  gate.
- `query_builder_offload_spec` now imports the sync QueryBuilder/core
  implementation directly so the executable spec covers the real storage
  offload methods instead of only the async-facing `std.database.query` shim.
- QueryBuilder row output stops being CPU-authoritative only when the measured
  native columnar-scan candidate row IDs match the QueryBuilder CPU row IDs.

The QueryBuilder SSD materialized projection slice consumes DBFS projected
row-value manifests at one query-facing boundary:

- `QueryBuilder.execute_with_ssd_materialized_projection` runs the existing
  QueryBuilder CPU row-ID oracle, validates a `DbfsSsdScanMaterialization`
  through the SSD materialized scan path, and returns projected SSD `SdnRow`
  values only after `gpu-cpu-row-match`.
- mismatched GPU candidate row IDs keep the returned rows on the existing
  `rows_for_ids` CPU path with `gpu-cpu-row-mismatch`.
- `query_builder_execute_with_ssd_materialized_projection` exports the same
  bounded path for callers that use the free-function QueryBuilder facade.
- `QueryBuilder.sum_i64_with_ssd_materialized_projection` consumes projected
  SSD numeric values for a bounded aggregate only after the same materialized
  scan validation succeeds; candidate mismatch keeps the aggregate on the CPU
  `sum_i64` path.
- `query_builder_sum_i64_with_ssd_materialized_projection` exports the bounded
  SSD aggregate path for free-function QueryBuilder callers.

The QueryBuilder filtered SUM aggregate slice expands live query operator
semantics beyond count-only aggregation:

- `QueryBuilderSumOffloadExecution` carries CPU-authoritative numeric SUM
  results beside storage-mode join/aggregate offload accounting.
- `QueryBuilder.sum_i64` computes filtered numeric sums over the existing
  QueryBuilder row path, preserving CPU result authority.
- `QueryBuilder.sum_i64_with_storage_offload` and
  `query_builder_sum_i64_with_storage_offload` route filtered SUM work through
  `DbStorageOffloadWorkload.JoinAggregate` and `gpu_db_join_aggregate_batch`.

The QueryBuilder MIN/MAX scalar aggregate slice expands the same bounded
operator family without claiming broad SQL kernel replacement:

- `QueryBuilderScalarOffloadExecution` and
  `QueryBuilderScalarDeviceOffloadExecution` carry CPU-authoritative scalar
  values beside storage-mode and measured-native device evidence.
- `QueryBuilder.min_i64` / `max_i64` compute filtered numeric scalar results
  over the existing QueryBuilder row path.
- `QueryBuilder.min_i64_with_storage_offload` and
  `QueryBuilder.max_i64_with_storage_offload` route filtered MIN/MAX work
  through `DbStorageOffloadWorkload.JoinAggregate` while preserving CPU result
  authority.
- `QueryBuilder.min_i64_with_device_backend_validated` and
  `QueryBuilder.max_i64_with_device_backend_validated` replace the scalar value
  only when a production device claim, CPU-oracle row IDs, and the scalar
  candidate agree; mismatched candidates fall back with
  `production-gpu-min-mismatch` or `production-gpu-max-mismatch`.
- `QueryBuilder.min_i64_with_ssd_materialized_projection` and
  `QueryBuilder.max_i64_with_ssd_materialized_projection` consume projected SSD
  numeric values only after materialized row-ID validation succeeds.
- `QueryBuilder.min_i64_with_ssd_materialized_projection_device_validated` and
  `QueryBuilder.max_i64_with_ssd_materialized_projection_device_validated`
  replace projected SSD scalar values only after production device evidence,
  QueryBuilder CPU row-ID agreement, materialized row-ID agreement, and scalar
  value agreement; mismatches fall back with `production-ssd-min-mismatch` or
  `production-ssd-max-mismatch`.
- `query_builder_offload_spec` now covers MIN/MAX storage accounting,
  measured-native MIN acceptance, measured-native MAX mismatch fallback, SSD
  projected MIN/MAX candidate consumption, and measured-native SSD projected
  MIN/MAX replacement/fallback.

The pure-SQL engine offload slice wires deeper SQL operators to the same
CPU-authoritative adapter evidence path:

- `PureSqlQueryOffloadExecution` returns pure-SQL rows, a
  `DbStorageOffloadExecution` evidence record, and `result_source`.
- `PureDatabase.query_with_offload_profile` parses SELECT once, runs the
  existing CPU SQL engine, and routes join, GROUP BY, and aggregate expressions
  through `sql_join_aggregate_offload_execute_profile` as
  `DbStorageOffloadWorkload.JoinAggregate` metadata.
- `PureDatabase.query_with_validated_offload_profile` is an opt-in sibling for
  bounded join/group-count and grouped `SUM(column)`, `MIN(column)`, and
  `MAX(column)` operators. It runs the
  existing CPU SQL oracle,
  builds a deterministic join/group aggregate candidate through the engine-owned
  input-row materializer, and only marks the offload envelope validated when the
  candidate rows match the CPU rows.
- all current join/aggregate SQL rows remain CPU-authoritative with
  `result_source: cpu_select`; GPU dispatch is reusable execution metadata
  until validated SQL GPU kernels can replace the CPU operator.
- validated Pure SQL candidates return `result_source:
  gpu_candidate_validated` while keeping CPU rows authoritative. This closes the
  previous `gpu-candidate-not-evaluated` gap for the supported grouped join
  count and grouped SUM/MIN/MAX shapes without claiming full hardware kernel
  replacement.
- measured-native grouped `MIN(column)` can replace Pure SQL result rows only
  after production device evidence, CPU SQL row agreement, and matching row IDs;
  mismatches remain CPU-authoritative through the existing SQL-row mismatch
  fallback.
- `sql_join_aggregate_offload_execute_validated` compares GPU candidate SQL
  rows against the CPU row oracle before accepting GPU dispatch evidence.
- `sql_join_aggregate_offload_execute_profile_validated` provides the same
  validation behavior for profile-driven Pure SQL callers.
- matching candidate rows set `gpu_candidate_validated=true` with
  `gpu-cpu-row-match`; mismatched candidates force CPU fallback with
  `gpu-cpu-row-mismatch` while preserving CPU rows.
- RAM-heavy profiles can dispatch eligible pure-SQL join/group/aggregate
  observations to `gpu_db_join_aggregate_batch`; SSD-accelerated observations
  still require current WAL-generation evidence.
- Pure SQL filtered projection SELECTs now route through
  `DbStorageOffloadWorkload.ScanFilterProject` and
  `gpu_db_columnar_scan_batch` while preserving CPU rows as authoritative.
- Pure SQL validated filtered projection SELECTs now compare bounded
  scan/filter/project GPU candidate row IDs with the CPU row oracle through
  `db_storage_execute_rows_validated`; matching candidates record
  `gpu-cpu-row-match`, while unavailable GPU dispatch keeps the result on
  `cpu_select`.
- `PureDatabase.query_with_device_backend_validated` is the strict native
  sibling for filtered projection SELECTs only. It routes scan/filter/project
  row IDs through `db_storage_execute_rows_with_device_backend_validated`, keeps
  joins/groups/aggregates out of this path, and only returns
  `result_source: production_gpu_candidate_validated` after measured native
  device timing plus CPU-oracle row-ID agreement.
- `pure_sql_offload_spec` covers filtered projection scan/filter/project,
  validated filtered projection scan/filter/project, strict native filtered
  projection replacement, JOIN, GROUP BY COUNT, grouped JOIN COUNT, validated
  grouped SUM, SUM,
  HAVING/ORDER/LIMIT aggregate routing, no-hardware fallback, and stale SSD
  aggregate fallback.

The DB offload profile slice adds reusable server profiles:

- `DbOffloadProfile` bundles registry targets, queue defaults, budget,
  GPU-availability evidence, and CPU fallback policy.
- `db_offload_profile_ram_heavy`, `db_offload_profile_ssd_accelerated`,
  `db_offload_profile_nosql_gpu`, `db_offload_profile_vector_gpu`, and
  `db_offload_profile_all_gpu` register the expected reusable GPU library
  targets for each DB server mode.
- `db_offload_profile_cpu_only` preserves CPU-authoritative fallback for
  maintenance or unavailable-GPU deployments.
- `db_offload_profile_execute` runs a `DbQueryOffloadRequest` through the query
  facade without duplicating registry/budget setup in each DB server path.
- `db_offload_profile_execute_scheduled` exposes scheduler-backed query
  execution at the profile layer for RAM-heavy, SSD-accelerated, NoSQL, and
  vector DB server modes.
- `db_offload_profile_execute_accumulating` exposes the accumulator-aware query
  path at the profile layer so DB servers can use named RAM/SSD/NoSQL/vector
  profiles without duplicating accumulator wiring.
- `db_offload_profile_execute_device` attaches strict
  `GpuWdbDeviceBackend` evidence to a normal `DbQueryOffloadRequest`, preserving
  CPU-authoritative query output while exposing production-device timing only
  for native backends with current registered targets.
- `db_offload_profile_execute_documents_device` exposes RAM NoSQL document
  measured-native replacement through the reusable NoSQL profile, advancing the
  profile queue from the same strict backend submission while preserving CPU
  authority on candidate mismatch.
- `db_offload_profile_flush_accumulator` and
  `db_offload_profile_flush_accumulator_current` flush accumulated DB profile
  work through the registered GPU library and profile queue, while preserving
  WAL/generation freshness evidence for SSD-accelerated batches.
- deferred profile work mutates `GpuWdbBatchAccumulator`, while GPU-worthy
  profile work dispatches immediately and leaves accumulator state unchanged.
- handled flushes reset accumulator state after GPU dispatch or CPU fallback;
  hard rejects retain accumulated work for reporting or retry.

The reusable web route adapter slice adds route-level GPU eligibility:

- `web_gpu_route_offload_execute` admits only coarse web payload work such as
  inference, embedding, ranking, and transform batches.
- GPU use is reported only when the matching target is registered:
  `gpu_web_inference_batch`, `gpu_web_embedding_batch`, `gpu_web_rank_batch`,
  or `gpu_web_transform_batch`.
- proxy forwarding and HTTP control-plane routes remain CPU fallback even when
  a misleading target is registered.
- CPU response status/body remain authoritative, so HTTP serialization and
  error handling stay in the worker/application path.
- `web_gpu_route_offload_execute_scheduled` consumes the shared scheduler before
  queue mutation so batch/background routes can defer tiny work to an
  accumulator while interactive routes keep CPU latency fallback.
- `web_gpu_route_offload_execute_accumulating` wires deferred web route work to
  `GpuWdbBatchAccumulator` while preserving CPU response status/body as the
  authoritative HTTP result.
- GPU-worthy web route batches bypass the accumulator and dispatch immediately;
  non-deferred routes return `route-not-deferred` with unchanged accumulator
  state.

The reusable web route profile slice adds server profile helpers:

- `WebGpuOffloadProfile` bundles registry targets, queue defaults, budgets,
  GPU-availability evidence, and CPU fallback policy.
- inference, embedding, rank, transform, all-web, and CPU-only profile builders
  provide reusable target sets for web application routes.
- `web_gpu_profile_execute` runs the route adapter without duplicating
  registry/budget setup in each controller or server path.
- `web_gpu_profile_execute_scheduled` exposes the scheduler-backed route path at
  the profile layer for controller/server adoption.
- `web_gpu_profile_execute_accumulating` exposes accumulator-aware execution at
  the profile layer so web server profiles can build coarse GPU batches without
  duplicating route accumulator wiring.
- `web_gpu_profile_flush_accumulator` and
  `web_gpu_profile_flush_accumulator_current` flush accumulated web profile work
  through the registered GPU library and profile queue.
- deferred profile work mutates `GpuWdbBatchAccumulator`, while GPU-worthy
  profile work dispatches immediately and leaves accumulator state unchanged.
- handled flushes reset accumulator state after GPU dispatch or CPU fallback;
  hard rejects retain accumulated web work for reporting or retry.
- proxy forwarding remains CPU-owned even when executed through an all-web GPU
  profile.
- `web_gpu_profile_execute_device_validated` is the strict response replacement
  sibling for web profiles. It requires a production `GpuWdbDeviceBackend`
  claim and matching CPU/GPU candidate status+body before a web route response
  stops being CPU-authoritative; mismatched candidates and perf-only backends
  retain the CPU response. Focused coverage now proves this replacement gate
  for inference, embedding, rank, and transform profile routes.

The web framework adapter slice adds controller-facing opt-in:

- `WebFrameworkGpuRouteConfig` binds a controller/action pair to a
  `WebGpuRouteKind` and default batch sizing.
- `web_framework_gpu_route_execute` reads optional `gpu_items` and
  `gpu_bytes_per_item` params from `ControllerContext`, delegates to the shared
  web route offload adapter, and returns the original `HttpResponseData` as the
  authoritative response.
- `web_framework_gpu_route_execute_scheduled` exposes the scheduler-backed route
  path to controllers so small batch/background work can be accumulated without
  making each controller duplicate queue policy.
- `web_framework_gpu_route_execute_accumulating` exposes the reusable
  `GpuWdbBatchAccumulator` path at the controller-facing API, preserving the
  controller's CPU response while mutating accumulator state for deferred work.
- GPU-worthy framework route work dispatches immediately through the registered
  GPU target and returns `route-not-deferred` with unchanged accumulator state.
- framework routes can now opt into inference, embedding, rank, or transform GPU
  accounting without duplicating queue/registry policy in each controller.
- `web_framework_gpu_route_execute_device_validated` exposes the web profile
  response replacement gate to controller-facing routes. It returns the GPU
  candidate `HttpResponseData` only after a production device claim and
  CPU/GPU status+body agreement; mismatches and perf-only backends preserve the
  controller CPU response.
- sync controller-facing transform routes now have focused strict replacement
  coverage through `web_framework_gpu_route_execute_device_validated`, proving
  non-inference framework responses stay CPU-owned on candidate mismatch.
- `WebApp` route helpers keep the embedded dispatcher router synchronized, so
  `WebApp.post(...).register_action(...).register_gpu_route(...).configure_gpu_profile(...)`
  flows through the real dispatcher GPU adoption path instead of only the lower
  level `AppDispatcher` API.

The sync HTTP server slice adds an initial worker-level reverse proxy path:

- `SimpleHttpServer` now has proxy route registration before normal router
  dispatch.
- proxy routes stream normal HTTP methods through a live upstream `TcpStream`
  instead of forcing the path through `fn(HttpRequest) -> HttpResponse`.
- the proxy request serializer rewrites `Host`, forces `Connection: close`,
  preserves query strings, adds forwarding headers, drops hop-by-hop headers,
  forwards parsed request bodies, and recomputes `Content-Length`.
- the proxy response path now reads upstream response headers separately, drops
  hop-by-hop response headers, forces client `Connection: close`, and then
  streams the response body with a max-byte guard.
- proxy routes now carry explicit upstream response header count and line-length
  limits so malformed or hostile backends fail closed before unbounded worker
  occupation.
- sync proxy response header handling validates upstream HTTP status lines
  before forwarding them to the client.
- sync proxy response header handling rejects malformed upstream header lines
  instead of silently dropping them.
- sync proxy response header handling parses upstream `Content-Length` and
  rejects declared bodies larger than `max_response_bytes` before body reads.
- sync proxy streaming rejects Upgrade/WebSocket requests with
  `NotImplemented` before opening an upstream, avoiding silent downgrade after
  hop-by-hop headers are stripped.
- sync proxy routes now carry a `max_buffered_request_body_bytes` guard so
  oversized fixed parsed request bodies switch to a header-first, bounded-slice
  upstream write path instead of building one full request wire.
- `reverse_proxy_serialize_request_headers`,
  `reverse_proxy_request_body_streaming_supported`, and
  `reverse_proxy_request_body_stream_chunk_count` make the sync fixed-body
  streaming branch testable while chunked and Upgrade traffic remain
  fail-closed.
- this slice remains close-delimited on the response side and still uses the
  sync parser's bounded in-memory request body for small fixed bodies. Raw
  socket-level client-body streaming, pooled upstream connections,
  WebSocket/Upgrade tunneling, and deeper async worker integration remain open
  work.

The async HTTP worker slice adds a nonblocking proxy state machine:

- proxy routes bypass the buffered `ContentHandler` path and start
  `AsyncProxyConnection` records in the worker event loop.
- the worker performs nonblocking upstream connect, request serialization,
  upstream response header/body receive, filtered client send, timeout reaping,
  and upstream/client fd cleanup.
- async proxy operations use worker op constants `OP_PROXY_CONNECT`,
  `OP_PROXY_SEND_REQUEST`, `OP_PROXY_RECV_RESPONSE`, and
  `OP_PROXY_SEND_CLIENT`.
- the async IO driver now handles connect operations with
  `submit_connect_timeout`.

The async proxy upstream policy slice adds reusable backend health selection:

- `AsyncProxyUpstreamPeer` tracks backend address, weight, fail budget,
  fail-timeout window, active connections, and last failure time.
- round-robin selection now skips unhealthy peers and reports a closed 502
  target when no healthy backend remains.
- least-connections selection uses weighted active-connection score so a worker
  can avoid already-busy backends.
- success/failure helpers reset or increment failure counters and release active
  connection counts.
- `async_proxy_select_server_with_peers` lets a worker apply explicit
  health/connection state while preserving the existing stateless config path.
- `Worker.proxy_upstream_peers` persists per-worker peer state keyed by backend
  address and feeds `async_proxy_plan_with_peers` before opening upstream
  connections.
- proxy connect/send/read failures and timeout reaping increment peer failure
  counters, while normal upstream EOF resets the failure count.
- proxy cleanup releases the active connection count exactly once for success,
  upstream failure, client-side close, and shutdown paths.
- `AsyncProxyHealthProbeDecision` records whether an upstream peer should be
  actively probed and why, without selecting a backend for a client request.
- `async_proxy_peer_probe_due` schedules active probes by interval and skips
  disabled or unusable peers.
- probe success/failure helpers update peer failure counters without changing
  active client connection counts.
- `AsyncProxyHealthProbeRecord` stores per-worker last-probe timestamps by
  upstream address.
- `async_proxy_due_health_probes` returns a capped list of due probes so one
  event-loop tick does not block on every backend.
- `async_proxy_mark_health_probe_attempt` updates or appends timestamp records
  after a worker starts an active probe.
- `Worker.proxy_health_probe_records` stores active-probe attempt timestamps
  next to worker-owned upstream peer health.
- worker helper methods expose due-probe planning, attempt recording, and
  probe success/failure application without changing live proxied request
  active-connection counts.
- the async `std.http_server` package explicitly re-exports the reverse proxy
  probe planner API for reuse by server code.
- `UpstreamConfig` now carries `health_check_interval_ms` and
  `health_check_max_probes` so active probing is configured per backend pool and
  remains disabled by default.
- `async_proxy_due_configured_health_probes` applies those upstream settings to
  worker-owned peer state and timestamp records.
- `parse_upstream` reads `health_check_interval` and
  `health_check_max_probes`; runtime coverage for block-style
  `parse_config_text` was deferred after recording
  `doc/08_tracking/bug/http_server_parse_config_text_block_sdn_2026-06-16.md`.

The async proxy response validation slice hardens upstream response handling:

- async proxy connections now carry per-response-header line and count budgets
  in addition to the total header-byte budget.
- `async_proxy_validate_response_headers` rejects missing or malformed status
  lines, invalid HTTP status codes, malformed header lines, excessive header
  count, and oversized header lines before client send.
- `async_proxy_prepare_client_chunk` marks completed malformed headers invalid
  without producing client data, and the worker turns that into a 502 error while
  marking the peer failure state.
- upstream responses with `Content-Length` larger than the configured response
  byte budget are rejected as soon as headers arrive, before the worker keeps
  reading an already-known oversized body.

The async proxy pool policy slice adds reusable upstream pooling rules:

- `AsyncProxyPoolEntry` records idle upstream fd, backend address, in-use state,
  closed state, last-used time, and reuse count.
- `async_proxy_pool_acquire` returns a reusable fd only for the same backend
  address when the entry is idle, open, under idle-timeout budget, and under
  max-reuse budget.
- release/close helpers update active state, last-used time, reuse count, and
  closed state without touching live sockets.
- per-upstream idle counts and caps define when a completed upstream connection
  can be retained for later reuse.
- `Worker.proxy_upstream_pool` now acquires reusable upstream fds before
  opening a fresh connection and releases safe completed responses back into the
  per-worker pool.

The async proxy response framing slice adds Content-Length completion detection:

- `AsyncProxyConnection` now tracks `expected_body_bytes`,
  `body_bytes_forwarded`, `response_complete`, `upstream_reusable`, and
  upstream request send progress.
- `async_proxy_content_length` parses case-insensitive upstream
  `Content-Length` headers and returns `-1` when a response is close-delimited.
- `async_proxy_response_complete` lets the worker stop upstream reads once the
  promised body bytes have been forwarded to the client.
- declared `Content-Length` is also checked against `max_response_bytes` early
  so framed oversized responses fail closed before body buffering.
- upstream requests now use `Connection: keep-alive`, but the worker releases an
  fd to the pool only when `async_proxy_response_reusable` confirms an HTTP/1.1
  framed response that did not ask to close.

The async proxy partial-write slice fixes production send correctness:

- `async_proxy_mark_request_sent` and `async_proxy_request_remaining` track
  upstream request bytes until the backend write fully completes.
- `async_proxy_remaining_after_send` keeps unsent downstream response bytes
  pending after a partial client write.
- the worker resubmits remaining upstream request or client response bytes
  before advancing the proxy state machine to the next receive.

The async proxy backpressure hardening slice makes flow control explicit:

- `AsyncProxyConnection` now carries a `max_pending_client_bytes` budget for
  client-bound bytes that have been decoded/read but not accepted by the client.
- `async_proxy_should_recv_upstream` centralizes the worker policy that upstream
  reads are scheduled only when no client bytes are pending and the response is
  still valid/incomplete.
- `async_proxy_pending_client_over_budget` fails closed if a slow client would
  leave too much response data queued in proxy state.
- `Worker.handle_proxy_recv_response` and `handle_proxy_send_client` now use
  these helpers before scheduling the next upstream read, making backpressure
  visible to tests instead of relying on an implicit branch shape.

The async proxy chunked-response slice fixes stripped transfer-encoding output:

- `async_proxy_transfer_chunked` detects upstream chunked responses before
  response headers are filtered.
- `async_proxy_dechunk_body` decodes complete chunked response bodies so the
  proxy does not forward raw chunk frames after removing `Transfer-Encoding`.
- `async_proxy_decode_available_chunks` streams decoded complete body chunks to
  the client while keeping only an incomplete chunk fragment in
  `chunked_body_buffer`.
- the first decoded chunk carries the filtered close-delimited response headers;
  later decoded chunks are sent as body-only pending client data.
- incomplete chunk fragments still respect `max_response_bytes` and fail closed
  before an upstream can grow residual chunk data without bound.
- this closes async proxy response dechunk buffering for large chunked upstream
  responses. Worker-integrated request-body streaming is now covered by the
  later live upload evidence; sync/proxy parity hardening remains separate
  follow-up work.

The proxy request transfer-encoding slice fails closed on unsupported request
body framing:

- async proxy planning rejects client requests with
  `Transfer-Encoding: chunked` before selecting or opening an upstream.
- async proxy planning rejects `Connection: Upgrade` / `Upgrade` requests before
  selecting or opening an upstream, so WebSocket traffic is not silently
  downgraded into normal GET proxying until tunnel support exists.
- sync proxy streaming rejects `Connection: Upgrade` / `Upgrade` requests with
  `NotImplemented` before selecting or opening an upstream.
- sync proxy streaming returns `NotImplemented` for chunked request bodies
  before connecting to the backend.
- fixed-length parsed request bodies continue to serialize with recomputed
  `Content-Length`.

The proxy request-body parity guard slice makes buffered-body limits explicit
on both sync and async proxy paths:

- sync proxy routes expose `max_buffered_request_body_bytes`; oversized fixed
  parsed bodies now use the sync fixed-body streaming branch instead of one full
  buffered request wire.
- async proxy planning exposes parameterized request-body limits for normal and
  peer-aware selection, returning `413 Proxy request body streaming required`
  before upstream selection for oversized fixed bodies.
- sync specs prove small fixed bodies remain on the buffered compatibility path
  while oversized fixed bodies are split into bounded upstream writes.
- async specs prove oversized fixed bodies still fail closed in normal planning
  while the worker-level stream planner owns the incremental upload path.
- this closes the unsafe unbounded full-buffer proxy-body parity gap without
  claiming raw request streaming or WebSocket tunneling support.

The async proxy request-body stream-state slice adds deterministic fixed and
chunked request transport evidence below the normal planning guard:

- `AsyncProxyRequestBodyStream` records header wire, pending upstream bytes,
  received body bytes, fixed/chunked mode, completion, validity, residual
  chunk buffer, and max pending upstream budget.
- `async_proxy_request_body_stream_begin` serializes upstream request headers
  without buffering the body, preserving either `Content-Length` or
  `Transfer-Encoding: chunked` framing for the worker state machine.
- `async_proxy_request_stream_receive_fixed` and
  `async_proxy_request_stream_receive_chunked` move client body bytes into
  upstream-pending data incrementally; chunked input is decoded before upstream
  writes so raw chunk frames are not forwarded after hop-by-hop filtering.
- `async_proxy_should_recv_client_body`,
  `async_proxy_request_pending_over_budget`, and
  `async_proxy_request_stream_mark_upstream_sent` make upstream write
  backpressure explicit before scheduling additional client-body reads.
- the normal async proxy planner still rejects oversized fixed bodies and
  chunked request bodies until the worker socket loop wires these stream states
  into live fd events.

The async proxy tunnel-planning slice separates tunnel setup from normal HTTP
proxying:

- `AsyncProxyTunnelPlan` records upstream resolution, status, reason, and tunnel
  kind for future worker-level CONNECT/WebSocket state machines.
- `async_proxy_tunnel_plan` and `async_proxy_tunnel_plan_with_peers` resolve
  CONNECT or Upgrade requests through the configured upstream pool without
  changing the normal HTTP proxy path, which still rejects upgrades fail-closed.
- `async_proxy_serialize_tunnel_request` rewrites `Host`, normalizes
  `Connection: Upgrade`, preserves `Upgrade` and WebSocket setup headers, and
  avoids normal hop-by-hop stripping for tunnel setup.
- full bidirectional socket relay remains open; this slice provides the tested
  setup contract for that worker integration.

The crash-recovery performance evidence slice adds deterministic benchmark row
coverage:

- `test/05_perf/web_db_offload/gpu_web_db_offload_bench_spec.spl` creates
  host-safe GPU-hit and CPU-fallback benchmark rows through the shared
  queue/library facades.
- The GPU-hit row reports backend, dataset, row count, vector dimensions,
  batch size, batch bytes, transfer bytes, kernel time, completion latency,
  p50/p95/p99, max RSS, queue depth, GPU hits, CPU fallbacks, timeout count,
  error count, and dispatch target.
- The tiny-batch row proves `batch-too-small` remains a CPU fallback and does
  not report transfer bytes, kernel time, queue reservation, or GPU hits.
- This closes the deterministic metrics-shape gap without claiming native or
  hardware GPU throughput.

The DB benchmark report slice adds repeatable RAM/persistent/WAL timing
evidence:

- `test/05_perf/db/db_bench_driver.spl` now isolates the persistent temp DB
  before timing so stale `/tmp` state cannot turn the benchmark into an omitted
  row.
- `MvccTxnManager._remove_active` no longer depends on `Array.remove`; it
  rebuilds the active transaction list explicitly, which lets the MVCC WAL
  count path produce trustworthy script and compiled timing rows.
- The emitted table labels DB configurations as `ram`, `persistent`, and `wal`
  instead of collapsing them under a generic script mode.
- `scripts/check/check-db-benchmark-report.shs` checks the driver, runs it, and
  verifies that both the dated report and persistent metrics table contain
  `db_ram_insert100`, `db_persistent_insert100`, and `db_wal_insert100` rows.
- `test/05_perf/db/db_wal_compiled_bench_driver.spl` is a standalone
  native-built WAL benchmark driver that validates `count_visible == 100` before
  recording compiled timing.
- `scripts/check/check-db-wal-compiled-benchmark-report.shs` builds that driver
  through `bin/simple native-build`, runs the compiled binary, and verifies the
  generated compiled WAL report and metrics table.
- `doc/09_report/perf/perf_baseline_db_2026-06-13.md` and
  `doc/10_metrics/perf/perf_baseline_db_table.md` now contain current
  x86_64 RAM, persistent deferred/checkpoint, and WAL timings.
- `doc/09_report/perf/perf_baseline_db_wal_compiled_2026-06-16.md` and
  `doc/10_metrics/perf/perf_baseline_db_wal_compiled_table.md` contain the
  native-built WAL timing row.

The production proxy benchmark evidence slice adds host-safe proxy metrics:

- `test/05_perf/web/proxy_reverse_proxy_bench_spec.spl` records deterministic
  benchmark rows for the production proxy helper path without opening sockets.
- The async row `async_proxy_policy_100` measures route planning, upstream
  request serialization, chunked response dechunk/forward policy, upstream reuse
  accounting, and explicit backpressure pauses across 100 iterations.
- The sync row `sync_proxy_helper_100` measures route matching, fixed-length
  request serialization, and response-header budget policy across 100
  iterations.
- The async request-stream row `async_proxy_request_stream_100` measures
  deterministic fixed request-body streaming, upstream pending-byte drain, and
  backpressure pauses across 100 iterations.
- The async tunnel row `async_proxy_tunnel_handshake_100` measures tunnel
  planning, setup serialization, upstream 101 validation, and relay-readiness
  state across 100 iterations without claiming full bidirectional socket relay.
- `scripts/check/check-proxy-benchmark-report.shs` checks the spec, runs it,
  regenerates the mirrored manual, and verifies all proxy benchmark rows are
  present, including policy, request-stream, tunnel-handshake, and sync helper
  rows.
- `test/05_perf/web/proxy_live_native_backend.spl` and
  `test/05_perf/web/proxy_live_native_cached_proxy.spl` are native-built by
  `scripts/check/check-proxy-live-socket-benchmark.shs` to add live cached
  Simple proxy throughput evidence alongside the Python reference loopback
  rows.
- the live native row `native_simple_cached_proxy_http_50` records p50/p95/p99,
  bytes, upstream reuse/connect counts, max RSS, timeout count, and error count
  for native-built Simple backend/proxy binaries on loopback sockets.
- `sh scripts/check/check-proxy-benchmark-report.shs` passed after verifying
  deterministic proxy benchmark rows and live cached Simple proxy throughput
  rows in the report and persistent metrics table.
- This closes deterministic production-proxy helper benchmark evidence,
  host-safe tunnel setup metrics, request-stream benchmark coverage, and live
  cached Simple proxy throughput row coverage. Sync streaming branch parity and
  full WebSocket/Upgrade bidirectional relay remain heavier follow-ups.

The framework route adoption slice wires the reusable web offload facade into a
real dispatcher path:

- `src/lib/nogc_sync_mut/web_framework/gpu_offload.spl` now exposes
  `web_framework_gpu_route_execute_for_action`, which scans controller/action
  GPU route configs, executes matched opt-in routes through the shared
  queue/library policy, and returns an explicit CPU-owned `no-gpu-route-config`
  result for unconfigured actions.
- `src/lib/nogc_async_mut/web_framework/dispatcher.spl` now carries optional
  GPU route configs, registry state, and a `dispatch_with_gpu_adoption` method
  that wraps the normal controller action result with offload evidence while
  keeping the controller response authoritative.
- `dispatch_with_gpu_validated_adoption` exposes the same strict response
  replacement gate at the dispatcher boundary without changing normal
  `dispatch`; configured actions can become non-CPU-authoritative only after
  production device timing and response agreement.
- `src/lib/nogc_async_mut/web_framework/app.spl` adds ergonomic
  `register_gpu_route` and `configure_gpu_offload` methods so application
  setup can opt specific controller actions into route GPU accounting.
- `test/01_unit/lib/nogc_async_mut/web_framework/dispatcher_spec.spl` proves a
  matched route records `gpu_web_rank_batch`, unconfigured actions remain
  CPU-owned control-plane work, and normal dispatcher errors are returned
  without fake GPU evidence.

Parallel review during this continuation:

- Spark reviewer `019ecf71-f1b7-7b82-94c1-c71d30a4f0ac` selected async
  dispatcher route adoption as the smallest high-value non-hardware slice and
  recommended proxy request-body streaming/backpressure as the next web/proxy
  follow-up after adoption.
- Normal reviewer `019ecf72-2191-7192-bab7-791248200f48` selected
  QueryBuilder row-query integration for RAM-only scan/filter/project as the
  next DB slice below the query offload facade, preserving CPU row order and
  results as authoritative.
- Spark reviewer `019ecfa4-8fc9-7e33-9dbe-0f78fcba9d22` confirmed
  `proxy_reverse_proxy_bench_spec.spl` plus
  `check-proxy-benchmark-report.shs` as the smallest non-tunnel slice for
  production proxy benchmark evidence and explicitly scoped live socket
  tunneling/throughput as a follow-up.

The QueryBuilder RAM-only row operator slice adds live row-query integration:

- `src/lib/nogc_sync_mut/database/query.spl` now exposes
  `QueryBuilderOffloadExecution`, extracts `execute_row_ids` and `rows_for_ids`
  so `execute()` and offload-aware execution share one CPU-authoritative row
  ordering path, and adds `execute_with_offload` plus
  `query_builder_execute_with_offload` for RAM-only scan/filter/project
  accounting.
- The implementation feeds CPU row IDs into `db_storage_execute_rows` with
  `DbStorageOffloadMode.RamOnly` and `ScanFilterProject`; GPU accounting is
  allowed only after the existing registry/budget/fallback gates accept it.
- `test/01_unit/lib/nogc_sync_mut/database/query_builder_offload_spec.spl`
  proves the same CPU query result order for sorted/limited rows while offload
  accounting reports GPU dispatch, tiny-batch fallback, or missing-target CPU
  fallback. The executable spec composes stable exported `QueryBuilder.execute`
  and `db_storage_execute_rows` surfaces because the interpreter did not resolve
  the newly added free-function wrapper during test execution even though
  `bin/simple check` accepts it.

The durable WAL freshness bridge slice connects SSD offload to engine state:

- `WriteAheadLog.pending_count` and `WriteAheadLog.generation_current` expose
  whether the durable WAL has entries beyond the flushed checkpoint sequence.
- `SdnDatabase.durable_wal_pending_count` and
  `SdnDatabase.durable_wal_generation_current` expose the same freshness signal
  from the database owner that loads/replays/checkpoints the WAL.
- `QueryBuilder.execute_with_storage_offload` and
  `query_builder_execute_with_storage_offload` add an explicit storage-mode
  sibling to the existing RAM-only offload API, so SSD callers can pass durable
  WAL freshness into `db_storage_execute_rows`.
- `storage_mode_offload_spec.spl` now proves stale SSD generations fall back and
  fresh SSD generations can dispatch through `gpu_db_columnar_scan_batch` while
  preserving CPU-authoritative row IDs.
- The attempted executable QueryBuilder SSD wrapper scenario hit the same
  interpreter resolution limitation as the earlier free-function wrapper; the
  production API checks clean and the executable evidence remains on the stable
  storage facade until that interpreter gap is fixed.

The DBFS SSD snapshot bridge moves SSD admission from a caller boolean to
engine-owned evidence:

- `DbfsSsdOffloadSnapshot` captures pager dirty count, WAL tail/durable LSN,
  checkpoint generation, B-tree generation, clean-checkpoint availability, and
  row batch size metadata.
- `dbfs_ssd_snapshot_current` admits SSD GPU accounting only when a clean
  checkpoint exists, no pager pages are dirty, the WAL tail is durable, and the
  checkpoint generation is not behind the namespace B-tree generation.
- `db_storage_execute_rows_for_ssd_snapshot` converts that DBFS evidence into
  the existing `DbStorageOffloadMode.SsdAccelerated` row-batch adapter without
  changing CPU-authoritative query semantics.
- `dbfs_ssd_offload_snapshot_spec.spl` proves current, dirty-pager,
  unflushed-WAL, stale-checkpoint, and storage-mode admission behavior.

The projected DBFS SSD materialization slice extends that bridge from row IDs
to scan metadata:

- `DbfsSsdScanMaterialization` now carries schema columns, projected columns,
  predicate text, row payload byte manifests, and projected row values alongside
  snapshot freshness and materialized row IDs.
- `dbfs_ssd_snapshot_materialize_projected_scan` validates projections against
  the schema before returning engine-owned scan evidence. The integration spec
  now writes page-cursor payload bytes and projected `id`/`amount` values, then
  asserts both the materialized payload byte manifest and projected row-value
  manifest.
- Projected SSD page-cursor materialized rows now feed the validated storage
  facade, so matching GPU candidate row IDs record `gpu-cpu-row-match` and
  mismatched candidates fall back with `gpu-cpu-row-mismatch`.
- QueryBuilder can now consume projected SSD row values after materialized-scan
  validation, turning the DBFS projected manifest into returned query rows for
  the bounded scan/filter/project path.
- `SdnTable.storage_row_batch_with_ssd_snapshot` lets table storage dispatch
  row batches directly from DBFS snapshot freshness evidence and
  `SdnTable.valid_row_ids`, instead of accepting a caller-supplied WAL boolean.
- `SdnTable.storage_row_batch_with_ssd_snapshot_validated` compares SSD table
  GPU candidate row IDs against `SdnTable.valid_row_ids`, accepting matching
  candidates and falling back to CPU-authoritative row IDs on mismatch.
- SSD table batches still preserve CPU-authoritative row IDs and fall back when
  the DBFS snapshot is dirty, stale, or otherwise unsafe.

The native/device timing provenance slice prepares the validated web/DB
offload path for real backend measurements without making an unsupported
hardware claim:

- `GpuWdbExecutionEvidence` now carries `device_time_us`,
  `device_timing_source`, and `backend_timing_valid` in addition to existing
  host-derived latency fields.
- `gpu_wdb_submission_evidence_with_device_timing` lets a future native
  backend/SFFI runner override `kernel_time_us` only when accepted GPU work has
  positive backend timing evidence.
- `gpu_web_db_offload_bench_spec.spl` now proves the existing host-safe vector
  and tiny-fallback rows stay unchanged and that a native timing probe row can
  carry explicit device timing provenance.
- `check-gpu-web-db-offload-native-device-probe.shs` is a fail-closed hardware
  gate: without valid `GPU_WDB_DEVICE_*` metrics it records unavailable or
  availability-only evidence; with the CUDA measured driver it records a
  measured `gpu_*` target row only after positive kernel, latency, and transfer
  metrics.

The runtime/SFFI timing bridge slice moves the timing source from a hardcoded
probe value to the host GPU queue runtime:

- `rt_host_gpu_queue_last_device_time_us` is exported through the Rust runtime,
  C native runtime, runtime symbol list, interpreter extern dispatch, runtime
  SFFI declarations, and ELF symbol lookup.
- Runtime queue completion records positive device time only for GPU-lane
  packets with a positive backend handle; unavailable GPU packets keep device
  time at zero.
- Existing payload accessors used by the runtime drain wrapper are now wired
  through the interpreter path, closing the `rt_host_gpu_queue_last_payload_*`
  registration gap exposed by the timing scenario.
- `host_gpu_event_path_spec.spl` now proves the timing SFFI directly after
  raw queue emit/submit/complete and still proves unavailable packets do not
  claim device time.
- `gpu_web_db_offload_bench_spec.spl` now sources the native timing probe row
  from `rt_host_gpu_queue_last_device_time_us()` instead of a fixed synthetic
  value.

The native backend availability and measured CUDA evidence slice adds runtime
backend discovery plus perf-only measured CUDA runners without claiming that
production DB operators have been replaced by GPU kernels:

- `gpu_web_db_offload_native_device_probe_driver.spl` prints machine-readable
  CUDA/Vulkan availability, device counts, and stable device labels.
- `gpu_web_db_offload_cuda_measured_driver.spl` launches a small CUDA
  sum-squares PTX kernel, validates the result against a CPU oracle, and emits
  `GPU_WDB_DEVICE_*` metrics for the validated vector-batch contract shape.
- `gpu_web_db_offload_columnar_scan_cuda_measured_driver.spl` launches a
  separate CUDA scan/filter/project checksum kernel, validates it against a CPU
  oracle, and emits measured evidence for the `gpu_db_columnar_scan_batch`
  contract shape used by Pure SQL scan/filter/project offload.
- `gpu_web_db_offload_native_device_probe_spec.spl` proves the probe classifies
  only `unavailable` or `available_unmeasured` before a measured kernel runner
  supplies positive timing and transfer metrics, and rejects fallback or
  zero-time rows as measured evidence.
- `check-gpu-web-db-offload-native-device-probe.shs` now checks, tests, and
  doc-generates that spec, runs the availability driver and vector measured
  CUDA driver, and writes the strongest valid evidence row into the probe
  report; the benchmark wrapper records both vector and columnar measured
  driver rows.
- On this host the interpreter-backed report records CUDA as `measured` for
  `gpu_db_vector_search_batch` with `cuda_device_count=2`,
  `kernel_time_us=176`, `completion_latency_us=176`, `transfer_bytes=8`, and
  `hardware_claim=native-device-measured`.
- The native-built probe driver now fails closed without crashing by using
  native C runtime availability stubs; it reports no native CUDA/Vulkan backend
  instead of claiming hardware execution.

## Verified

- `bin/simple check src/lib/nogc_sync_mut/web_db_offload/contract.spl src/lib/nogc_sync_mut/web_db_offload/__init__.spl test/01_unit/lib/nogc_sync_mut/web_db_offload/gpu_web_db_offload_contract_spec.spl test/03_system/lib/web_db_offload/feature/gpu_web_db_offload_spec.spl`
- `bin/simple test test/01_unit/lib/nogc_sync_mut/web_db_offload/gpu_web_db_offload_contract_spec.spl --mode=interpreter`
  - 12 tests passed.
- `bin/simple test test/03_system/lib/web_db_offload/feature/gpu_web_db_offload_spec.spl --mode=interpreter`
  - 7 scenarios passed.
- `bin/simple spipe-docgen test/01_unit/lib/nogc_sync_mut/web_db_offload/gpu_web_db_offload_contract_spec.spl --output doc/06_spec`
- `bin/simple spipe-docgen test/03_system/lib/web_db_offload/feature/gpu_web_db_offload_spec.spl --output doc/06_spec`
- `bin/simple check src/lib/nogc_sync_mut/database/vector/offload_plan.spl src/lib/nogc_sync_mut/database/vector/__init__.spl test/01_unit/lib/nogc_sync_mut/database/vector/vector_offload_plan_spec.spl`
- `bin/simple test test/01_unit/lib/nogc_sync_mut/database/vector/vector_offload_plan_spec.spl --mode=interpreter`
  - 5 tests passed.
- `bin/simple spipe-docgen test/01_unit/lib/nogc_sync_mut/database/vector/vector_offload_plan_spec.spl --output doc/06_spec`
- `bin/simple check src/lib/nogc_sync_mut/database/gpu_mode_plan.spl src/lib/nogc_sync_mut/database/__init__.spl test/01_unit/lib/nogc_sync_mut/database/gpu_mode_plan_spec.spl`
- `bin/simple test test/01_unit/lib/nogc_sync_mut/database/gpu_mode_plan_spec.spl --mode=interpreter`
  - 5 tests passed.
- `bin/simple spipe-docgen test/01_unit/lib/nogc_sync_mut/database/gpu_mode_plan_spec.spl --output doc/06_spec`
- `bin/simple check src/lib/nogc_sync_mut/http_server/proxy.spl src/lib/nogc_sync_mut/http_server/server.spl src/lib/nogc_sync_mut/http_server/__init__.spl test/01_unit/lib/nogc_sync_mut/http_server/reverse_proxy_spec.spl`
- `bin/simple test test/01_unit/lib/nogc_sync_mut/http_server/reverse_proxy_spec.spl --mode=interpreter`
  - 15 tests passed.
- `bin/simple spipe-docgen test/01_unit/lib/nogc_sync_mut/http_server/reverse_proxy_spec.spl --output doc/06_spec`
- `bin/simple check src/lib/nogc_sync_mut/database/db_offload.spl src/lib/nogc_sync_mut/database/__init__.spl test/01_unit/lib/nogc_sync_mut/database/db_gpu_batch_offload_spec.spl src/lib/nogc_sync_mut/database/nosql_offload.spl test/01_unit/lib/nogc_sync_mut/database/nosql_document_offload_spec.spl src/lib/nogc_sync_mut/database/vector/search_offload.spl test/01_unit/lib/nogc_sync_mut/database/vector/vector_search_offload_adapter_spec.spl src/lib/nogc_sync_mut/web_db_offload/library.spl src/lib/nogc_sync_mut/web_db_offload/queue.spl test/01_unit/lib/nogc_sync_mut/web_db_offload/gpu_web_db_offload_library_spec.spl`
- `bin/simple test test/01_unit/lib/nogc_sync_mut/database/db_gpu_batch_offload_spec.spl --mode=interpreter`
  - 5 tests passed.
- `bin/simple test test/01_unit/lib/nogc_sync_mut/database/nosql_document_offload_spec.spl --mode=interpreter`
  - 4 tests passed.
- `bin/simple test test/01_unit/lib/nogc_sync_mut/database/vector/vector_search_offload_adapter_spec.spl --mode=interpreter`
  - 3 tests passed.
- `bin/simple check src/lib/nogc_sync_mut/database/vector/store.spl src/lib/nogc_sync_mut/database/vector/__init__.spl src/lib/nogc_sync_mut/database/query_offload.spl test/01_unit/lib/nogc_sync_mut/database/vector/vector_store_search_offload_spec.spl`
  - passed after adding vector store accumulated search offload.
- `SIMPLE_LIB=src bin/simple test test/01_unit/lib/nogc_sync_mut/database/vector/vector_store_search_offload_spec.spl --mode=interpreter --clean`
  - 6 tests passed.
- `SIMPLE_LIB=src bin/simple spipe-docgen test/01_unit/lib/nogc_sync_mut/database/vector/vector_store_search_offload_spec.spl --output doc/06_spec --no-index`
  - generated 1 complete doc with the pre-existing short-doc warning.
- `bin/simple test test/01_unit/lib/nogc_sync_mut/web_db_offload/gpu_web_db_offload_library_spec.spl --mode=interpreter`
  - 3 tests passed.
- `bin/simple spipe-docgen test/01_unit/lib/nogc_sync_mut/database/db_gpu_batch_offload_spec.spl --output doc/06_spec`
- `bin/simple check src/lib/nogc_sync_mut/web_db_offload/scheduler.spl src/lib/nogc_sync_mut/web_db_offload/__init__.spl test/01_unit/lib/nogc_sync_mut/web_db_offload/gpu_web_db_offload_scheduler_spec.spl`
- `bin/simple test test/01_unit/lib/nogc_sync_mut/web_db_offload/gpu_web_db_offload_scheduler_spec.spl --mode=interpreter`
  - 12 tests passed after adding registered accumulator flush coverage.
- `bin/simple spipe-docgen test/01_unit/lib/nogc_sync_mut/web_db_offload/gpu_web_db_offload_scheduler_spec.spl --output doc/06_spec`
  - generated 1 complete doc with short-doc summary warnings.
- `bin/simple check src/lib/nogc_sync_mut/web_db_offload/web_route.spl src/lib/nogc_sync_mut/web_db_offload/__init__.spl test/01_unit/lib/nogc_sync_mut/web_db_offload/web_route_gpu_offload_spec.spl`
- `bin/simple test test/01_unit/lib/nogc_sync_mut/web_db_offload/web_route_gpu_offload_spec.spl --mode=interpreter`
  - 9 tests passed.
- `bin/simple spipe-docgen test/01_unit/lib/nogc_sync_mut/web_db_offload/web_route_gpu_offload_spec.spl --output doc/06_spec`
- `bin/simple check src/lib/nogc_sync_mut/web_db_offload/web_profile.spl src/lib/nogc_sync_mut/web_db_offload/web_route.spl src/lib/nogc_sync_mut/web_db_offload/__init__.spl test/01_unit/lib/nogc_sync_mut/web_db_offload/web_route_profile_spec.spl`
- `bin/simple test test/01_unit/lib/nogc_sync_mut/web_db_offload/web_route_profile_spec.spl --mode=interpreter`
  - 11 tests passed after adding web profile accumulator flush coverage.
- `bin/simple spipe-docgen test/01_unit/lib/nogc_sync_mut/web_db_offload/web_route_profile_spec.spl --output doc/06_spec`
  - generated 1 complete doc with the pre-existing short-doc warning.
- `bin/simple check src/lib/nogc_async_mut/http_server/types.spl src/lib/nogc_async_mut/http_server/config.spl src/lib/nogc_async_mut/http_server/proxy.spl src/lib/nogc_async_mut/http_server/worker.spl src/lib/nogc_async_mut/http_server/__init__.spl test/01_unit/lib/nogc_async_mut/http_server/async_reverse_proxy_spec.spl`
- `bin/simple test test/01_unit/lib/nogc_async_mut/http_server/async_reverse_proxy_spec.spl --mode=interpreter`
  - 44 tests passed.
- `bin/simple spipe-docgen test/01_unit/lib/nogc_async_mut/http_server/async_reverse_proxy_spec.spl --output doc/06_spec`
- `bin/simple check src/lib/nogc_async_mut/http_server/proxy.spl test/01_unit/lib/nogc_async_mut/http_server/async_reverse_proxy_spec.spl`
- `SIMPLE_LIB=src bin/simple test test/01_unit/lib/nogc_async_mut/http_server/async_reverse_proxy_spec.spl --mode=interpreter`
  - 44 tests passed after adding async streaming dechunk coverage.
- `SIMPLE_LIB=src bin/simple spipe-docgen test/01_unit/lib/nogc_async_mut/http_server/async_reverse_proxy_spec.spl --output doc/06_spec --no-index`
  - generated 1 complete doc with the pre-existing short-doc warning.
- `bin/simple check src/lib/nogc_async_mut/http_server/proxy.spl src/lib/nogc_async_mut/http_server/worker.spl test/01_unit/lib/nogc_async_mut/http_server/async_reverse_proxy_spec.spl`
- `SIMPLE_LIB=src bin/simple test test/01_unit/lib/nogc_async_mut/http_server/async_reverse_proxy_spec.spl --mode=interpreter`
  - 45 tests passed after adding explicit client backpressure policy coverage.
- `SIMPLE_LIB=src bin/simple spipe-docgen test/01_unit/lib/nogc_async_mut/http_server/async_reverse_proxy_spec.spl --output doc/06_spec --no-index`
  - generated 1 complete doc with the pre-existing short-doc warning.
- `bin/simple check src/lib/nogc_sync_mut/web_framework/gpu_offload.spl src/lib/nogc_sync_mut/web_framework/__init__.spl test/01_unit/lib/nogc_sync_mut/web_framework/gpu_offload_spec.spl`
- `bin/simple test test/01_unit/lib/nogc_sync_mut/web_framework/gpu_offload_spec.spl --mode=interpreter`
  - 9 tests passed after adding accumulator-aware controller API coverage.
- `bin/simple spipe-docgen test/01_unit/lib/nogc_sync_mut/web_framework/gpu_offload_spec.spl --output doc/06_spec`
  - generated 1 complete doc with the pre-existing short-doc warning.
- `bin/simple check src/lib/nogc_sync_mut/web_framework/gpu_offload.spl src/lib/nogc_sync_mut/web_framework/__init__.spl src/lib/nogc_async_mut/web_framework/dispatcher.spl src/lib/nogc_async_mut/web_framework/app.spl src/lib/nogc_async_mut/web_framework/__init__.spl test/01_unit/lib/nogc_sync_mut/web_framework/gpu_offload_spec.spl test/01_unit/lib/nogc_async_mut/web_framework/dispatcher_spec.spl`
  - passed with one pre-existing async `app.spl` `gc_boundary_crossing` warning.
- `SIMPLE_LIB=src bin/simple test test/01_unit/lib/nogc_async_mut/web_framework/dispatcher_spec.spl --mode=interpreter`
  - 3 tests passed.
- `SIMPLE_LIB=src bin/simple spipe-docgen test/01_unit/lib/nogc_sync_mut/web_framework/gpu_offload_spec.spl test/01_unit/lib/nogc_async_mut/web_framework/dispatcher_spec.spl --output doc/06_spec --no-index`
  - generated 2 complete docs with short-doc summary warnings only.
- `bin/simple check src/lib/nogc_sync_mut/database/storage_mode_offload.spl src/lib/nogc_sync_mut/database/__init__.spl test/01_unit/lib/nogc_sync_mut/database/storage_mode_offload_spec.spl`
- `bin/simple test test/01_unit/lib/nogc_sync_mut/database/storage_mode_offload_spec.spl --mode=interpreter`
  - 5 tests passed.
- `bin/simple spipe-docgen test/01_unit/lib/nogc_sync_mut/database/storage_mode_offload_spec.spl --output doc/06_spec`
- `bin/simple check src/lib/nogc_sync_mut/database/query_offload.spl src/lib/nogc_sync_mut/database/storage_mode_offload.spl src/lib/nogc_sync_mut/database/__init__.spl test/01_unit/lib/nogc_sync_mut/database/db_query_offload_spec.spl`
- `bin/simple test test/01_unit/lib/nogc_sync_mut/database/db_query_offload_spec.spl --mode=interpreter`
  - 9 tests passed after adding join/aggregate accumulator coverage.
- `bin/simple spipe-docgen test/01_unit/lib/nogc_sync_mut/database/db_query_offload_spec.spl --output doc/06_spec`
- `bin/simple check src/lib/nogc_sync_mut/database/query.spl src/lib/nogc_sync_mut/database/__init__.spl test/01_unit/lib/nogc_sync_mut/database/query_builder_offload_spec.spl`
- `SIMPLE_LIB=src bin/simple test test/01_unit/lib/nogc_sync_mut/database/query_builder_offload_spec.spl --mode=interpreter`
  - 3 tests passed.
- `SIMPLE_LIB=src bin/simple test test/01_unit/lib/database/database_query_spec.spl --mode=interpreter`
  - 6 tests passed from the runner cache after the final query implementation shape.
- `SIMPLE_LIB=src bin/simple spipe-docgen test/01_unit/lib/nogc_sync_mut/database/query_builder_offload_spec.spl --output doc/06_spec --no-index`
  - generated 1 complete doc with a short-doc summary warning only.
- `bin/simple check src/lib/nogc_sync_mut/database/wal.spl src/lib/nogc_sync_mut/database/core.spl src/lib/nogc_sync_mut/database/query.spl src/lib/nogc_sync_mut/database/__init__.spl test/01_unit/lib/nogc_sync_mut/database/storage_mode_offload_spec.spl test/01_unit/lib/nogc_sync_mut/database/query_builder_offload_spec.spl`
- `SIMPLE_LIB=src bin/simple test test/01_unit/lib/nogc_sync_mut/database/storage_mode_offload_spec.spl --mode=interpreter`
  - 6 tests passed after adding fresh SSD-generation dispatch coverage.
- `SIMPLE_LIB=src bin/simple test test/01_unit/lib/nogc_sync_mut/database/query_builder_offload_spec.spl --mode=interpreter`
  - 3 tests passed after retaining stable RAM-only executable coverage.
- `SIMPLE_LIB=src bin/simple spipe-docgen test/01_unit/lib/nogc_sync_mut/database/storage_mode_offload_spec.spl test/01_unit/lib/nogc_sync_mut/database/query_builder_offload_spec.spl --output doc/06_spec --no-index`
  - generated 2 complete docs with short-doc warnings only.
- `bin/simple check src/lib/nogc_sync_mut/database/query.spl src/lib/nogc_sync_mut/database/__init__.spl test/01_unit/lib/nogc_sync_mut/database/query_builder_offload_spec.spl`
  - passed after adding `QueryBuilderAggregateOffloadExecution` and aggregate
    count offload exports.
- `SIMPLE_LIB=src bin/simple test test/01_unit/lib/nogc_sync_mut/database/query_builder_offload_spec.spl --mode=interpreter`
  - 4 tests passed after adding join/aggregate accounting evidence.
- `bin/simple spipe-docgen test/01_unit/lib/nogc_sync_mut/database/query_builder_offload_spec.spl --output doc/06_spec --no-index`
  - generated 1 complete doc with a short-doc summary warning only.
- `bin/simple check src/lib/nogc_sync_mut/database/query.spl src/lib/nogc_sync_mut/database/query_offload.spl src/lib/nogc_sync_mut/database/__init__.spl test/01_unit/lib/nogc_sync_mut/database/query_builder_offload_spec.spl test/01_unit/lib/nogc_sync_mut/database/db_query_offload_spec.spl`
  - passed after adding QueryBuilder aggregate accumulator APIs and query-facade
    join/aggregate accumulator coverage.
- `SIMPLE_LIB=src bin/simple test test/01_unit/lib/nogc_sync_mut/database/query_builder_offload_spec.spl --mode=interpreter --clean`
  - 4 tests passed.
- `SIMPLE_LIB=src bin/simple test test/01_unit/lib/nogc_sync_mut/database/db_query_offload_spec.spl --mode=interpreter --clean`
  - 9 tests passed.
- `SIMPLE_LIB=src bin/simple spipe-docgen test/01_unit/lib/nogc_sync_mut/database/query_builder_offload_spec.spl test/01_unit/lib/nogc_sync_mut/database/db_query_offload_spec.spl --output doc/06_spec --no-index`
  - generated 2 complete docs with short-doc warnings only.
- `bin/simple check src/lib/nogc_sync_mut/database/pure_sql/database_part2.spl src/lib/nogc_sync_mut/database/pure_sql/__init__.spl test/01_unit/lib/nogc_sync_mut/database/pure_sql_offload_spec.spl`
  - passed after adding `PureDatabase.query_with_offload_profile`.
- `SIMPLE_LIB=src bin/simple test test/01_unit/lib/nogc_sync_mut/database/pure_sql_offload_spec.spl --mode=interpreter`
  - 3 tests passed.
- `SIMPLE_LIB=src bin/simple test test/02_integration/storage/dbfs/pure_db_spec.spl --mode=interpreter`
  - 63 tests passed.
- `SIMPLE_LIB=src bin/simple test test/02_integration/storage/dbfs/pure_db_sql_extended_spec.spl --mode=interpreter`
  - 10 tests passed.
- `bin/simple spipe-docgen test/01_unit/lib/nogc_sync_mut/database/pure_sql_offload_spec.spl --output doc/06_spec --no-index`
  - generated 1 complete doc; first pass had short-doc/syntax/research manual
    warnings, then the spec manual metadata was expanded.
- `bin/simple check src/lib/nogc_sync_mut/database/pure_sql/database_part2.spl test/01_unit/lib/nogc_sync_mut/database/pure_sql_offload_spec.spl`
  - passed after adding the pre-CPU pure-SQL join/aggregate offload result seam
    and `result_source` reporting.
- `bin/simple test test/01_unit/lib/nogc_sync_mut/database/pure_sql_offload_spec.spl --mode=interpreter`
  - 4 tests passed, including accepted grouped COUNT and accepted grouped
    inner-join COUNT rows from `gpu_join_aggregate`.
- `SIMPLE_LIB=src bin/simple spipe-docgen test/01_unit/lib/nogc_sync_mut/database/pure_sql_offload_spec.spl --output doc/06_spec --no-index`
  - generated 1 complete doc with existing docgen warnings outside this lane
    and one short-doc warning.
- `bin/simple check src/lib/nogc_sync_mut/database/offload_profile.spl src/lib/nogc_sync_mut/database/query_offload.spl src/lib/nogc_sync_mut/database/__init__.spl test/01_unit/lib/nogc_sync_mut/database/db_offload_profile_spec.spl`
- `bin/simple test test/01_unit/lib/nogc_sync_mut/database/db_offload_profile_spec.spl --mode=interpreter`
  - 11 tests passed after adding DB profile accumulator flush coverage.
- `bin/simple spipe-docgen test/01_unit/lib/nogc_sync_mut/database/db_offload_profile_spec.spl --output doc/06_spec`
  - generated 1 complete doc with the pre-existing short-doc warning.
- `bin/simple check test/05_perf/web_db_offload/gpu_web_db_offload_bench_spec.spl`
- `SIMPLE_LIB=src bin/simple test test/05_perf/web_db_offload/gpu_web_db_offload_bench_spec.spl --mode=interpreter`
  - 2 tests passed.
- `SIMPLE_LIB=src bin/simple spipe-docgen test/05_perf/web_db_offload/gpu_web_db_offload_bench_spec.spl --output doc/06_spec --no-index`
  - generated 1 complete doc with one short-doc warning.
- `bin/simple check test/05_perf/db/db_bench_driver.spl test/05_perf/db/db_ram_vs_persistent_bench_spec.spl test/05_perf/db/wal_disk_replay_repro_spec.spl`
- `SIMPLE_LIB=src bin/simple test test/05_perf/db/db_ram_vs_persistent_bench_spec.spl --mode=interpreter`
  - 13 tests passed.
- `SIMPLE_LIB=src bin/simple test test/05_perf/db/wal_disk_replay_repro_spec.spl --mode=interpreter`
  - 1 test passed.
- `scripts/check/check-db-benchmark-report.shs`
  - `STATUS: PASS db benchmark report`; regenerated RAM and persistent
    x86_64 rows in the dated report and persistent metrics table.
- `bin/simple check test/05_perf/web/proxy_reverse_proxy_bench_spec.spl`
- `SIMPLE_LIB=src bin/simple test test/05_perf/web/proxy_reverse_proxy_bench_spec.spl --mode=interpreter`
  - 3 tests passed after adding async request-stream benchmark evidence.
- `scripts/check/check-proxy-benchmark-report.shs`
  - `STATUS: PASS proxy benchmark report`; regenerated the mirrored proxy
    benchmark manual with the pre-existing short-doc/missing-syntax warnings.
- `bin/simple check src/lib/nogc_sync_mut/http_server/proxy.spl test/01_unit/lib/nogc_sync_mut/http_server/reverse_proxy_spec.spl`
  - passed after adding sync buffered request-body limit policy.
- `bin/simple check src/lib/nogc_async_mut/http_server/proxy.spl test/01_unit/lib/nogc_async_mut/http_server/async_reverse_proxy_spec.spl`
  - passed after adding async request-body streaming-required planning policy.
- `SIMPLE_LIB=src bin/simple test test/01_unit/lib/nogc_sync_mut/http_server/reverse_proxy_spec.spl --mode=interpreter`
  - 17 tests passed.
- `SIMPLE_LIB=src bin/simple test test/01_unit/lib/nogc_async_mut/http_server/async_reverse_proxy_spec.spl --mode=interpreter`
  - 51 tests passed after adding async tunnel planning coverage.
- `bin/simple spipe-docgen test/01_unit/lib/nogc_sync_mut/http_server/reverse_proxy_spec.spl test/01_unit/lib/nogc_async_mut/http_server/async_reverse_proxy_spec.spl --output doc/06_spec --no-index`
  - generated 2 complete docs with short-doc warnings only.
- `bin/simple check src/lib/nogc_async_mut/http_server/proxy.spl test/01_unit/lib/nogc_async_mut/http_server/async_reverse_proxy_spec.spl`
  - passed after adding `AsyncProxyTunnelPlan`.
- `SIMPLE_LIB=src bin/simple test test/01_unit/lib/nogc_async_mut/http_server/async_reverse_proxy_spec.spl --mode=interpreter --clean`
  - 51 tests passed.
- `SIMPLE_LIB=src bin/simple spipe-docgen test/01_unit/lib/nogc_async_mut/http_server/async_reverse_proxy_spec.spl --output doc/06_spec --no-index`
  - generated 1 complete doc with the pre-existing short-doc warning.
- `bin/simple check src/lib/nogc_async_mut/http_server/proxy.spl test/01_unit/lib/nogc_async_mut/http_server/async_reverse_proxy_spec.spl test/05_perf/web/proxy_reverse_proxy_bench_spec.spl`
  - passed after adding async request-body stream state helpers and benchmark
    evidence.
- `SIMPLE_LIB=src bin/simple test test/01_unit/lib/nogc_async_mut/http_server/async_reverse_proxy_spec.spl --mode=interpreter`
  - 54 tests passed.
- `bin/simple spipe-docgen test/01_unit/lib/nogc_async_mut/http_server/async_reverse_proxy_spec.spl`
  - generated 1 complete doc with the existing short-doc warning.
- `sh scripts/check/check-proxy-benchmark-report.shs`
  - `STATUS: PASS proxy benchmark report`; requires
    `async_proxy_request_stream_100`.
- `bin/simple check src/lib/nogc_sync_mut/database/nosql_offload.spl src/lib/nogc_sync_mut/database/__init__.spl test/01_unit/lib/nogc_sync_mut/database/nosql_document_offload_spec.spl`
  - passed after adding the RAM document collection metadata-filter path.
- `SIMPLE_LIB=src bin/simple test test/01_unit/lib/nogc_sync_mut/database/nosql_document_offload_spec.spl --mode=interpreter`
  - 6 tests passed.
- `bin/simple spipe-docgen test/01_unit/lib/nogc_sync_mut/database/nosql_document_offload_spec.spl --output doc/06_spec --no-index`
  - generated 1 complete doc; first pass had a missing-overview warning that
    was fixed in the spec metadata.
- `bin/simple check src/lib/nogc_sync_mut/database/core.spl src/lib/nogc_sync_mut/database/nosql_offload.spl src/lib/nogc_sync_mut/database/__init__.spl test/01_unit/lib/nogc_sync_mut/database/storage_row_batch_offload_spec.spl test/01_unit/lib/nogc_sync_mut/database/nosql_document_offload_spec.spl`
  - passed after adding RAM table storage batch manifests.
- `SIMPLE_LIB=src bin/simple test test/01_unit/lib/nogc_sync_mut/database/storage_row_batch_offload_spec.spl --mode=interpreter`
  - 6 tests passed after adding SSD mode/freshness coverage.
- `bin/simple spipe-docgen test/01_unit/lib/nogc_sync_mut/database/storage_row_batch_offload_spec.spl test/01_unit/lib/nogc_sync_mut/database/nosql_document_offload_spec.spl --output doc/06_spec --no-index`
  - generated 2 complete docs; first pass had a missing examples/syntax warning
    for the storage row manual that was fixed in the spec metadata.
- `bin/simple check src/lib/nogc_sync_mut/database/core.spl src/lib/nogc_sync_mut/database/storage_mode_offload.spl test/01_unit/lib/nogc_sync_mut/database/storage_row_batch_offload_spec.spl`
  - passed after adding `SdnTable.storage_row_batch_with_mode_offload`.
- `SIMPLE_LIB=src bin/simple test test/01_unit/lib/nogc_sync_mut/database/storage_row_batch_offload_spec.spl --mode=interpreter --clean`
  - 6 tests passed.
- `SIMPLE_LIB=src bin/simple spipe-docgen test/01_unit/lib/nogc_sync_mut/database/storage_row_batch_offload_spec.spl --output doc/06_spec --no-index`
  - generated 1 complete doc with the pre-existing short-doc warning.
- `bin/simple check src/lib/nogc_sync_mut/database/nosql_offload.spl test/01_unit/lib/nogc_sync_mut/database/nosql_document_offload_spec.spl`
  - passed after aligning durable NoSQL collection saves with the existing
    write-at-offset file primitive.
- `SIMPLE_LIB=src bin/simple test test/01_unit/lib/nogc_sync_mut/database/nosql_document_offload_spec.spl --mode=interpreter`
  - 7 tests passed, including durable collection save/load feeding
    CPU-authoritative metadata IDs into document-filter offload accounting.
- `bin/simple spipe-docgen test/01_unit/lib/nogc_sync_mut/database/nosql_document_offload_spec.spl`
  - generated 1 complete doc with existing docgen warnings outside this lane.
- `bin/simple check src/lib/nogc_sync_mut/db/dbfs_engine/ns_btree.spl src/lib/nogc_sync_mut/db/dbfs_engine/offload_snapshot.spl src/lib/nogc_sync_mut/db/dbfs_engine/__init__.spl src/lib/nogc_sync_mut/database/storage_mode_offload.spl src/lib/nogc_sync_mut/database/__init__.spl test/02_integration/storage/dbfs/dbfs_ssd_offload_snapshot_spec.spl`
  - passed after adding DBFS SSD snapshot admission evidence.
- `SIMPLE_LIB=src bin/simple test test/02_integration/storage/dbfs/dbfs_ssd_offload_snapshot_spec.spl --mode=interpreter`
  - 5 tests passed.
- `bin/simple spipe-docgen test/02_integration/storage/dbfs/dbfs_ssd_offload_snapshot_spec.spl`
  - generated 1 complete doc with existing docgen warnings outside this lane.
- `bin/simple check src/lib/nogc_sync_mut/db/dbfs_engine/mvcc.spl test/05_perf/db/db_bench_driver.spl test/05_perf/db/db_wal_compiled_bench_driver.spl`
  - passed after replacing `MvccTxnManager._remove_active` `Array.remove` usage
    with explicit active-list rebuilding and adding the compiled WAL benchmark
    driver.
- `SIMPLE_LIB=src bin/simple test test/02_integration/storage/dbfs/dbfs_mvcc_visibility_spec.spl --mode=interpreter --clean`
  - 17 tests passed after the MVCC transaction cleanup change.
- `sh scripts/check/check-db-wal-compiled-benchmark-report.shs`
  - `STATUS: PASS db wal compiled benchmark report`; native-built
    `test/05_perf/db/db_wal_compiled_bench_driver.spl`, ran the compiled binary,
    and generated `doc/09_report/perf/perf_baseline_db_wal_compiled_2026-06-16.md`
    plus `doc/10_metrics/perf/perf_baseline_db_wal_compiled_table.md`.
- `sh scripts/check/check-db-benchmark-report.shs`
  - `STATUS: PASS db benchmark report`; now requires script-mode RAM,
    persistent, and WAL rows plus the separate native-built WAL timing report.
- `bin/simple check src/lib/nogc_async_mut/http_server/proxy.spl test/01_unit/lib/nogc_async_mut/http_server/async_reverse_proxy_spec.spl`
  - passed after adding reusable async proxy tunnel connection state helpers.
- `SIMPLE_LIB=src bin/simple test test/01_unit/lib/nogc_async_mut/http_server/async_reverse_proxy_spec.spl --mode=interpreter --clean`
  - 57 tests passed, including tunnel setup partial writes, bidirectional
    relay buffers, and per-direction backpressure budget coverage.
- `SIMPLE_LIB=src bin/simple spipe-docgen test/01_unit/lib/nogc_async_mut/http_server/async_reverse_proxy_spec.spl --output doc/06_spec --no-index`
  - generated 1 complete doc with existing docgen warnings outside this lane
    and one short-doc warning.
- `bin/simple check src/lib/nogc_sync_mut/http_server/proxy.spl test/01_unit/lib/nogc_sync_mut/http_server/reverse_proxy_spec.spl`
  - passed after adding sync fixed-body header-first bounded-slice upstream
    writes.
- `SIMPLE_LIB=src bin/simple test test/01_unit/lib/nogc_sync_mut/http_server/reverse_proxy_spec.spl --mode=interpreter`
  - 18 tests passed.
- `bin/simple spipe-docgen test/01_unit/lib/nogc_sync_mut/http_server/reverse_proxy_spec.spl`
  - generated 1 complete doc with the existing short-doc warning.
- `bin/simple check src/lib/nogc_async_mut/http_server/proxy.spl src/lib/nogc_async_mut/http_server/worker.spl test/01_unit/lib/nogc_async_mut/http_server/async_reverse_proxy_spec.spl`
  - passed after adding worker-owned fixed `Content-Length` request-body
    streaming state, header-first upstream writes, and a distinct
    `OP_PROXY_SEND_REQUEST_BODY` scheduling branch.
- `SIMPLE_LIB=src bin/simple test test/01_unit/lib/nogc_async_mut/http_server/async_reverse_proxy_spec.spl --mode=interpreter`
  - 59 tests passed, including the worker streaming planner contract that
    allows oversized fixed bodies to select a healthy backend without using the
    fully buffered compatibility planner.
- `SIMPLE_LIB=src bin/simple spipe-docgen test/01_unit/lib/nogc_async_mut/http_server/async_reverse_proxy_spec.spl --output doc/06_spec --no-index`
  - generated 1 complete doc with the existing short-doc warning.
- `bin/simple check src/lib/nogc_async_mut/http_server/proxy.spl src/lib/nogc_async_mut/http_server/worker.spl src/lib/nogc_async_mut/http_server/__init__.spl test/01_unit/lib/nogc_async_mut/http_server/async_reverse_proxy_spec.spl`
  - passed after wiring worker-level tunnel op dispatch and binary-safe
    post-setup tunnel payload buffers.
- `SIMPLE_LIB=src bin/simple test test/01_unit/lib/nogc_async_mut/http_server/async_reverse_proxy_spec.spl --mode=interpreter --clean`
  - 60 tests passed, including in-flight read suppression and binary WebSocket
    / CONNECT payload preservation across partial sends.
- `SIMPLE_LIB=src bin/simple spipe-docgen test/01_unit/lib/nogc_async_mut/http_server/async_reverse_proxy_spec.spl --output doc/06_spec --no-index`
  - regenerated 1 complete doc with existing docgen warnings outside this lane
    and one short-doc warning.
- `bin/simple check src/lib/nogc_async_mut/http_server/proxy.spl src/lib/nogc_async_mut/http_server/worker.spl test/01_unit/lib/nogc_async_mut/http_server/async_reverse_proxy_spec.spl`
  - passed after enabling chunked request bodies on the worker streaming
    planner and adding a dechunked upstream header/body stream helper.
- `SIMPLE_LIB=src bin/simple test test/01_unit/lib/nogc_async_mut/http_server/async_reverse_proxy_spec.spl --mode=interpreter`
  - 61 tests passed, including worker-streaming planner coverage for chunked
    bodies and dechunked upstream body data with a `Content-Length` header.
- `SIMPLE_LIB=src bin/simple spipe-docgen test/01_unit/lib/nogc_async_mut/http_server/async_reverse_proxy_spec.spl --output doc/06_spec --no-index`
  - regenerated 1 complete doc with existing docgen warnings outside this lane
    and one short-doc warning.
- `bin/simple check src/lib/nogc_async_mut/http_server/proxy.spl src/lib/nogc_async_mut/http_server/worker.spl src/lib/nogc_async_mut/http_server/__init__.spl test/01_unit/lib/nogc_async_mut/http_server/async_reverse_proxy_spec.spl`
  - passed after tightening upstream `101 Switching Protocols` validation for
    upgrade tunnels to require `Connection: Upgrade` as a comma token and a
    non-empty `Upgrade` header, while preserving payload bytes that arrive with
    the final upstream header fragment.
- `SIMPLE_LIB=src bin/simple test test/01_unit/lib/nogc_async_mut/http_server/async_reverse_proxy_spec.spl --mode=interpreter`
  - 67 tests passed, including valid/invalid upstream upgrade handshakes,
    comma-token `Connection` handling, and split-header payload preservation.
- `SIMPLE_LIB=src bin/simple spipe-docgen test/01_unit/lib/nogc_async_mut/http_server/async_reverse_proxy_spec.spl --output doc/06_spec --no-index`
  - regenerated 1 complete doc with existing docgen warnings outside this lane
    and one short-doc warning.
- `bin/simple check src/lib/nogc_async_mut/http_server/connection.spl src/lib/nogc_async_mut/http_server/worker.spl test/01_unit/lib/nogc_async_mut/http_server/async_reverse_proxy_spec.spl`
  - passed after preserving raw client bytes that arrive in the same recv as
    the parsed Upgrade/CONNECT request headers and queuing them into the tunnel
    after upstream handshake completion.
- `SIMPLE_LIB=src bin/simple test test/01_unit/lib/nogc_async_mut/http_server/async_reverse_proxy_spec.spl --mode=interpreter --clean`
  - 68 tests passed, including the coalesced upgrade-header payload carry case.
- `SIMPLE_LIB=src bin/simple spipe-docgen test/01_unit/lib/nogc_async_mut/http_server/async_reverse_proxy_spec.spl --output doc/06_spec --no-index`
  - regenerated 1 complete doc with existing docgen warnings outside this lane
    and one short-doc warning.
- `sh scripts/check/check-proxy-benchmark-report.shs`
  - `STATUS: PASS proxy benchmark report`; now requires
    `async_proxy_tunnel_handshake_100` in addition to async policy, async
    request streaming, and sync helper rows. It also runs
    `scripts/check/check-proxy-live-socket-benchmark.shs`, which opens
    loopback sockets for `live_socket_proxy_http_cached_50` and
    `live_socket_proxy_tunnel_50`, native-builds and runs
    `native_simple_cached_proxy_http_50`, writes
    `doc/09_report/perf/proxy_live_socket_benchmark_2026-06-16.md`, and mirrors
    stable metrics to `doc/10_metrics/perf/proxy_live_socket_benchmark.md`.
    The cached HTTP row records p50/p95/p99, bytes, upstream reuse/connect
    counts, max RSS, timeout count, and error count; the tunnel row records the
    same latency/RSS/error shape with zero upstream reuse because Upgrade
    tunnels are not pooled. The native Simple row is labeled
    `native_simple_cached_proxy_loopback` and records the same latency/RSS/error
    shape with `upstream_connects=1` and `upstream_reuse=49`.
- `find doc/06_spec -name '*_spec.spl' | wc -l` prints `0`.
- `jj git fetch` reports `Nothing changed.`
- `bin/simple check src/lib/nogc_sync_mut/database/query_offload.spl src/lib/nogc_sync_mut/database/query.spl src/lib/nogc_sync_mut/database/sql_join_aggregate_offload.spl src/lib/nogc_sync_mut/database/pure_sql/database_part2.spl src/lib/nogc_sync_mut/database/__init__.spl test/01_unit/lib/nogc_sync_mut/database/db_query_offload_spec.spl test/01_unit/lib/nogc_sync_mut/database/query_builder_offload_spec.spl test/01_unit/lib/nogc_sync_mut/database/sql_join_aggregate_offload_adapter_spec.spl test/01_unit/lib/nogc_sync_mut/database/pure_sql_offload_spec.spl`
  - passed after adding `SqlJoinAggregateOffloadExecution`, the reusable SQL
    join/aggregate adapter, and query-facade aggregate result metadata.
- `SIMPLE_LIB=src bin/simple test test/01_unit/lib/nogc_sync_mut/database/sql_join_aggregate_offload_adapter_spec.spl --mode=interpreter --clean`
  - 3 tests passed: registered join/aggregate GPU dispatch, no-hardware CPU
    fallback, and stale-WAL CPU fallback, all with CPU-authoritative rows.
- `SIMPLE_LIB=src bin/simple test test/01_unit/lib/nogc_sync_mut/database/db_query_offload_spec.spl --mode=interpreter --clean`
  - 10 tests passed, including the reusable SQL aggregate count result wrapper
    over `db_query_offload_execute`.
- `SIMPLE_LIB=src bin/simple test test/01_unit/lib/nogc_sync_mut/database/query_builder_offload_spec.spl --mode=interpreter --clean`
  - 4 tests passed; QueryBuilder row/order/count behavior remains
    CPU-authoritative while matching row offload accounting is preserved.
- `SIMPLE_LIB=src bin/simple test test/01_unit/lib/nogc_sync_mut/database/pure_sql_offload_spec.spl --mode=interpreter --clean`
  - 7 tests passed after Pure SQL join/aggregate SELECTs were wired through
    the adapter and expanded to cover SUM plus HAVING/ORDER/LIMIT aggregate
    routing while keeping CPU SQL rows authoritative.
- `SIMPLE_LIB=src bin/simple spipe-docgen test/01_unit/lib/nogc_sync_mut/database/sql_join_aggregate_offload_adapter_spec.spl test/01_unit/lib/nogc_sync_mut/database/db_query_offload_spec.spl test/01_unit/lib/nogc_sync_mut/database/query_builder_offload_spec.spl test/01_unit/lib/nogc_sync_mut/database/pure_sql_offload_spec.spl --output doc/06_spec --no-index`
  - generated 4 complete docs with short-document warnings only.
- `bin/simple check src/lib/nogc_sync_mut/database/query_offload.spl src/lib/nogc_sync_mut/database/__init__.spl test/01_unit/lib/nogc_sync_mut/database/db_query_offload_spec.spl`
  - passed after adding the DBFS SSD snapshot query-facade helper and coverage.
- `SIMPLE_LIB=src bin/simple test test/01_unit/lib/nogc_sync_mut/database/db_query_offload_spec.spl --mode=interpreter --clean`
  - 14 tests passed, including SSD snapshot scan/filter/project dispatch,
    join/aggregate dispatch, stale DBFS snapshot CPU fallback, and document
    workload rejection.
- `SIMPLE_LIB=src bin/simple spipe-docgen test/01_unit/lib/nogc_sync_mut/database/db_query_offload_spec.spl --output doc/06_spec --no-index`
  - regenerated 1 complete doc with existing docgen warnings outside this lane
    and one short-doc warning.
- `src/compiler_rust/target/debug/simple check src/lib/nogc_sync_mut/database/core.spl src/lib/nogc_sync_mut/database/storage_mode_offload.spl src/lib/nogc_sync_mut/db/dbfs_engine/offload_snapshot.spl test/01_unit/lib/nogc_sync_mut/database/storage_row_batch_offload_spec.spl test/02_integration/storage/dbfs/dbfs_ssd_offload_snapshot_spec.spl`
  - passed after adding projected DBFS SSD scan metadata and the `SdnTable`
    snapshot-backed storage batch helper.
- `SIMPLE_LIB=src src/compiler_rust/target/debug/simple test test/01_unit/lib/nogc_sync_mut/database/storage_row_batch_offload_spec.spl --mode=interpreter --clean`
  - 8 tests passed, including clean DBFS snapshot table-batch dispatch and
    stale snapshot CPU fallback.
- `SIMPLE_LIB=src src/compiler_rust/target/debug/simple test test/02_integration/storage/dbfs/dbfs_ssd_offload_snapshot_spec.spl --mode=interpreter --clean`
  - 11 tests passed, including schema/projection/predicate metadata carry and
    unknown projected-column rejection.
- `SIMPLE_LIB=src src/compiler_rust/target/debug/simple test test/01_unit/lib/nogc_sync_mut/database/db_query_offload_spec.spl --mode=interpreter --clean`
  - 17 tests passed after the projected SSD materialization update.
- `SIMPLE_LIB=src src/compiler_rust/target/debug/simple spipe-docgen test/01_unit/lib/nogc_sync_mut/database/storage_row_batch_offload_spec.spl --output doc/06_spec --no-index`
  - regenerated 1 complete doc with existing docgen warnings.
- `SIMPLE_LIB=src src/compiler_rust/target/debug/simple spipe-docgen test/02_integration/storage/dbfs/dbfs_ssd_offload_snapshot_spec.spl --output doc/06_spec --no-index`
  - regenerated 1 complete doc with existing docgen warnings.
- `src/compiler_rust/target/debug/simple check src/lib/nogc_sync_mut/web_db_offload/queue.spl test/05_perf/web_db_offload/gpu_web_db_offload_bench_spec.spl`
  - passed after adding backend device timing provenance fields and the native
    timing helper.
- `SIMPLE_LIB=src src/compiler_rust/target/debug/simple test test/05_perf/web_db_offload/gpu_web_db_offload_bench_spec.spl --mode=interpreter --clean`
  - 3 tests passed, including the native timing provenance row.
- `SIMPLE_LIB=src src/compiler_rust/target/debug/simple spipe-docgen test/05_perf/web_db_offload/gpu_web_db_offload_bench_spec.spl --output doc/06_spec --no-index`
  - regenerated 1 complete doc with the existing short-document warning.
- `sh scripts/check/check-gpu-web-db-offload-native-device-probe.shs`
  - `STATUS: PASS gpu web/db native device probe`; generated fail-closed
    unavailable hardware evidence rows without claiming throughput.
- `sh scripts/check/check-gpu-web-db-offload-benchmark-report.shs`
  - `STATUS: PASS gpu web/db offload benchmark report`; now includes
    host-safe, native timing provenance, measured CUDA vector-batch, and tiny
    CPU-fallback rows.
- `src/compiler_rust/target/debug/simple check src/lib/nogc_sync_mut/web_db_offload/queue.spl src/lib/nogc_sync_mut/web_db_offload/library.spl test/01_unit/lib/nogc_sync_mut/web_db_offload/gpu_web_db_offload_library_spec.spl test/01_unit/lib/nogc_sync_mut/web_db_offload/gpu_web_db_offload_scheduler_spec.spl`
  - passed for the shared registry/scheduler evidence boundary.
- `SIMPLE_LIB=src src/compiler_rust/target/debug/simple test test/01_unit/lib/nogc_sync_mut/web_db_offload/gpu_web_db_offload_library_spec.spl --mode=interpreter --clean`
  - 3 tests passed.
- `SIMPLE_LIB=src src/compiler_rust/target/debug/simple test test/01_unit/lib/nogc_sync_mut/web_db_offload/gpu_web_db_offload_scheduler_spec.spl --mode=interpreter --clean`
  - 14 tests passed.
- `cargo build --manifest-path src/compiler_rust/Cargo.toml --bin simple`
  - passed after wiring the host GPU queue timing and payload accessors.
- `cargo test --manifest-path src/compiler_rust/Cargo.toml -p simple-runtime host_gpu_lane --lib -- --test-threads=1`
  - 6 runtime host GPU queue tests passed, including unavailable zero timing
    and positive backend completion timing.
- `src/compiler_rust/target/debug/simple check test/03_system/feature/language/host_gpu_event_path_spec.spl test/05_perf/web_db_offload/gpu_web_db_offload_bench_spec.spl`
  - passed after adding the runtime timing SFFI assertions.
- `SIMPLE_LIB=src src/compiler_rust/target/debug/simple test test/03_system/feature/language/host_gpu_event_path_spec.spl --mode=interpreter --clean --sequential`
  - 7 examples passed, including direct runtime device timing after backend
    completion.
- `SIMPLE_LIB=src src/compiler_rust/target/debug/simple test test/05_perf/web_db_offload/gpu_web_db_offload_bench_spec.spl --mode=interpreter --clean --sequential`
  - 3 examples passed; the native timing provenance row now reads runtime queue
    device timing.
- `SIMPLE_LIB=src src/compiler_rust/target/debug/simple spipe-docgen test/03_system/feature/language/host_gpu_event_path_spec.spl --output doc/06_spec --no-index`
  - regenerated 1 complete doc with the existing short-document warning.
- `SIMPLE_LIB=src src/compiler_rust/target/debug/simple spipe-docgen test/05_perf/web_db_offload/gpu_web_db_offload_bench_spec.spl --output doc/06_spec --no-index`
  - regenerated 1 complete doc with the existing short-document warning.
- `sh scripts/check/check-gpu-web-db-offload-benchmark-report.shs`
  - `STATUS: PASS gpu web/db offload benchmark report`; wrapper now runs this
    shared runtime queue spec sequentially, honors `SIMPLE_BIN`, and writes
    measured CUDA rows for both `gpu_db_vector_search_batch` and
    `gpu_db_columnar_scan_batch`.
- `sh scripts/check/check-gpu-web-db-offload-native-device-probe.shs`
  - `STATUS: PASS gpu web/db native device probe`.
- `sh scripts/check/check-gpu-web-db-offload-benchmark-report.shs`
  - `STATUS: PASS gpu web/db offload benchmark report`; generated
    `db_columnar_scan_cuda_measured | cuda | pure_sql_scan_filter_project |
    gpu_db_columnar_scan_batch | device_time_us=152 |
    native-device-measured` from the independent columnar scan CUDA driver.
- `sh scripts/check/check-gpu-web-db-offload-native-device-probe.shs`
  - `STATUS: PASS gpu web/db native device probe`; measured-row validation now
    accepts positive timing for both DB vector and DB columnar scan GPU targets.
- `src/compiler_rust/target/debug/simple check src/app/mcp`
  - passed: 30 files.
- `src/compiler_rust/target/debug/simple check src/app/simple_lsp_mcp`
  - passed: 4 files.
- `src/compiler_rust/target/debug/simple check src/compiler`
  - attempted with a 300s cap; timed out with no final output.
- `src/compiler_rust/target/debug/simple check src/lib`
  - attempted with a 300s cap; timed out with no final output.
- `src/compiler_rust/target/debug/simple check test/05_perf/web_db_offload/gpu_web_db_offload_native_device_probe_spec.spl test/05_perf/web_db_offload/gpu_web_db_offload_native_device_probe_driver.spl`
  - passed after adding runtime CUDA/Vulkan availability probe coverage.
- `SIMPLE_LIB=src src/compiler_rust/target/debug/simple test test/05_perf/web_db_offload/gpu_web_db_offload_native_device_probe_spec.spl --mode=interpreter --clean --sequential`
  - 2 examples passed.
- `sh scripts/check/check-gpu-web-db-offload-native-device-probe.shs`
  - `STATUS: PASS gpu web/db native device probe`; report now records
    `available_unmeasured` CUDA availability on this host without a throughput
    claim.
- `src/compiler_rust/target/debug/simple check test/05_perf/web_db_offload/gpu_web_db_offload_cuda_measured_driver.spl`
  - passed after adding the perf-only CUDA measured vector-batch runner.
- `timeout 45 src/compiler_rust/target/debug/simple run test/05_perf/web_db_offload/gpu_web_db_offload_cuda_measured_driver.spl`
  - passed and emitted `GPU_WDB_DEVICE_STATUS=measured`,
    `GPU_WDB_DEVICE_TARGET=gpu_db_vector_search_batch`, positive CUDA kernel
    time, positive completion latency, and `native-device-measured`.
- `sh scripts/check/check-gpu-web-db-offload-native-device-probe.shs`
  - `STATUS: PASS gpu web/db native device probe`; report now prefers the
    measured CUDA runner row and records `measured | cuda | cuda-device-0 |
    gpu_db_vector_search_batch | kernel_time_us=176 |
    hardware_claim=native-device-measured`.
- `src/compiler_rust/target/debug/simple native-build --source src/compiler --source src/lib --entry test/05_perf/web_db_offload/gpu_web_db_offload_native_device_probe_driver.spl --output build/gpu_web_db_offload_native_device_probe`
  - passed.
- `./build/gpu_web_db_offload_native_device_probe`
  - passed and returned fail-closed native runtime availability:
    `cuda_available=0`, `vulkan_available=0`, no hardware claim.
- `bin/simple check src/lib/nogc_async_mut/http_server/proxy.spl src/lib/nogc_async_mut/http_server/worker.spl src/lib/nogc_async_mut/http_server/__init__.spl test/01_unit/lib/nogc_async_mut/http_server/async_reverse_proxy_spec.spl`
  - passed after adding fixed-length early proxy handoff at header completion,
    a distinct `OP_PROXY_RECV_CLIENT_BODY` worker op, and client-body recv
    scheduling that waits for upstream request-body writes to drain.
- `SIMPLE_LIB=src bin/simple test test/01_unit/lib/nogc_async_mut/http_server/async_reverse_proxy_spec.spl --mode=interpreter --clean`
  - 70 tests passed, including header-complete parsing for oversized fixed
    proxy uploads before the normal parser buffers the full body.
- `SIMPLE_LIB=src bin/simple spipe-docgen test/01_unit/lib/nogc_async_mut/http_server/async_reverse_proxy_spec.spl --output doc/06_spec --no-index`
  - regenerated 1 complete doc with the existing short-document warning.
- `bin/simple check src/lib/nogc_sync_mut/web_db_offload/queue.spl src/lib/nogc_sync_mut/web_db_offload/__init__.spl test/01_unit/lib/nogc_sync_mut/web_db_offload/gpu_web_db_offload_contract_spec.spl test/05_perf/web_db_offload/gpu_web_db_offload_bench_spec.spl`
  - passed after adding reusable `GpuWdbExecutionEvidence` and
    `gpu_wdb_submission_evidence` so web and DB callers can report transfer
    bytes, kernel time, completion latency, queue depth, GPU hits, CPU
    fallbacks, stream id, pinned bytes, and fallback reason from one shared
    queue-library API.
- `SIMPLE_LIB=src bin/simple test test/01_unit/lib/nogc_sync_mut/web_db_offload/gpu_web_db_offload_contract_spec.spl --mode=interpreter --clean`
  - 17 tests passed, including accepted GPU evidence rows and CPU fallback
    evidence rows without fake transfer or kernel time.
- `SIMPLE_LIB=src bin/simple test test/05_perf/web_db_offload/gpu_web_db_offload_bench_spec.spl --mode=interpreter --clean`
  - 2 tests passed; the host-safe GPU web/DB perf contract now consumes the
    reusable evidence API instead of deriving benchmark fields ad hoc.
- `bin/simple check test/01_unit/lib/nogc_sync_mut/web_db_offload/gpu_web_db_offload_contract_spec.spl`
  - passed after expanding the contract spec manual header with requirements,
    plan, design, research, and examples.
- `SIMPLE_LIB=src bin/simple spipe-docgen test/01_unit/lib/nogc_sync_mut/web_db_offload/gpu_web_db_offload_contract_spec.spl test/05_perf/web_db_offload/gpu_web_db_offload_bench_spec.spl --output doc/06_spec --no-index`
  - regenerated 2 complete docs; remaining warnings are short-document warnings
    only plus existing docgen/runtime warnings outside this lane.
- `sh scripts/check/check-gpu-web-db-offload-benchmark-report.shs`
  - `STATUS: PASS gpu web/db offload benchmark report`; checks and runs
    `gpu_web_db_offload_bench_spec.spl`, regenerates the mirrored manual, and
    writes `doc/09_report/perf/gpu_web_db_offload_benchmark_2026-06-16.md`
    plus `doc/10_metrics/perf/gpu_web_db_offload_benchmark.md`.
  - the report records `db_vector_gpu_hit` and
    `web_embedding_tiny_cpu_fallback` rows with `host-safe-mock` backend and
    `hardware_claim=none-host-safe-contract`, so it proves report shape and
    fallback accounting without claiming native/hardware GPU throughput.
- `bin/simple check src/lib/nogc_sync_mut/database/storage_mode_offload.spl src/lib/nogc_sync_mut/database/query_offload.spl src/lib/nogc_sync_mut/database/sql_join_aggregate_offload.spl src/lib/nogc_sync_mut/database/pure_sql/database_part2.spl test/01_unit/lib/nogc_sync_mut/database/sql_join_aggregate_offload_adapter_spec.spl test/01_unit/lib/nogc_sync_mut/database/pure_sql_offload_spec.spl test/01_unit/lib/nogc_sync_mut/database/db_query_offload_spec.spl`
  - passed after promoting GPU candidate validation metadata into
    `DbStorageOffloadExecution` and updating all DB offload envelope
    construction sites.
- `SIMPLE_LIB=src bin/simple test test/01_unit/lib/nogc_sync_mut/database/sql_join_aggregate_offload_adapter_spec.spl --mode=interpreter --clean`
  - 5 tests passed; SQL adapter evidence now records validation state in both
    the adapter result and shared offload envelope.
- `SIMPLE_LIB=src bin/simple test test/01_unit/lib/nogc_sync_mut/database/pure_sql_offload_spec.spl --mode=interpreter --clean`
  - 7 tests passed; Pure SQL join/aggregate paths now expose deterministic
    shared validation metadata while keeping CPU rows authoritative.
- `SIMPLE_LIB=src bin/simple test test/01_unit/lib/nogc_sync_mut/database/db_query_offload_spec.spl --mode=interpreter --clean`
  - 14 tests passed; generic query facade rows and fallbacks carry explicit
    `gpu-candidate-not-evaluated` metadata until a CPU/GPU row candidate
    comparison is available.
- `SIMPLE_LIB=src bin/simple spipe-docgen test/01_unit/lib/nogc_sync_mut/database/sql_join_aggregate_offload_adapter_spec.spl test/01_unit/lib/nogc_sync_mut/database/pure_sql_offload_spec.spl test/01_unit/lib/nogc_sync_mut/database/db_query_offload_spec.spl --output doc/06_spec --no-index`
  - regenerated 3 complete docs with existing docgen warnings outside this lane
    and short-doc warnings only.
- `bin/simple check src/lib/nogc_sync_mut/database/storage_mode_offload.spl src/lib/nogc_sync_mut/database/__init__.spl test/01_unit/lib/nogc_sync_mut/database/storage_mode_offload_spec.spl`
  - passed after adding storage-facade validated GPU candidate manifests for
    row IDs and document IDs.
- `SIMPLE_LIB=src bin/simple test test/01_unit/lib/nogc_sync_mut/database/storage_mode_offload_spec.spl --mode=interpreter --clean`
  - 11 tests passed, including RAM row candidate match/mismatch, fresh SSD row
    candidate validation, and NoSQL document candidate match/mismatch.
- `SIMPLE_LIB=src bin/simple spipe-docgen test/01_unit/lib/nogc_sync_mut/database/storage_mode_offload_spec.spl --output doc/06_spec --no-index`
  - regenerated 1 complete doc with existing docgen warnings outside this lane
    and one short-document warning.
- `sh scripts/check/check-proxy-live-httpserver.shs`
  - added a native real-`HttpServer` reverse proxy fixture at
    `test/05_perf/web/proxy_live_httpserver_proxy.spl` and a raw-socket check
    wrapper that starts a backend process, builds the fixture, configures
    `LocationConfig.proxy_pass` plus `UpstreamConfig`, and verifies backend body
    forwarding, hop-by-hop filtering, and rewritten Host headers.
  - 2026-06-16 follow-up fixed the production-path blocker and now passes with
    `SIMPLE_BIN=src/compiler_rust/target/debug/simple`: `STATUS: PASS proxy
    live HttpServer reverse proxy`.
  - fixes applied in this lane include guarded `Worker.reap_expired`,
    `IoDriver` accept polling, native `rt_event_loop_register` ABI alignment,
    native `rt_text_to_bytes` / `rt_bytes_to_text`, native statement-match
    extraction for nested enum tuple payloads (`Ok((location, params))`),
    native-safe `AsyncRouter.route` loops, direct prefix route return params,
    worker-side proxy stream storage that avoids native dict misdispatch, an
    empty-pool guard before `async_proxy_pool_acquire`, native-safe upstream
    status validation without `starts_with`, and response filtering that drops
    hop-by-hop headers without appending `Connection: close`.
  - the wrapper still reports two unrelated non-critical entry-closure skips
    (`http/h2/h2_hpack.spl` and `security/auth/context_propagation.spl`) and
    unresolved-symbol stubs from the broader native closure. The fixture itself
    passes and verifies two backend requests, rewritten upstream Host headers,
    backend body forwarding, and response hop-by-hop filtering.
- `bin/simple check src/lib/nogc_sync_mut/database/sql_join_aggregate_offload.spl test/01_unit/lib/nogc_sync_mut/database/sql_join_aggregate_offload_adapter_spec.spl`
  - passed after adding SQL join/aggregate GPU candidate row validation.
- `SIMPLE_LIB=src bin/simple test test/01_unit/lib/nogc_sync_mut/database/sql_join_aggregate_offload_adapter_spec.spl --mode=interpreter --clean`
  - 5 tests passed, including accepted matching GPU candidate rows and rejected
    mismatched GPU candidate rows with CPU fallback.
- `SIMPLE_LIB=src bin/simple test test/01_unit/lib/nogc_sync_mut/database/pure_sql_offload_spec.spl --mode=interpreter --clean`
  - 8 tests passed after adding
    `PureDatabase.query_with_validated_offload_profile`; grouped join aggregate
    candidate rows now compare against the CPU SQL oracle and report
    `gpu-cpu-row-match` with `result_source: gpu_candidate_validated`.
- `SIMPLE_LIB=src bin/simple test test/01_unit/lib/nogc_sync_mut/database/db_query_offload_spec.spl --mode=interpreter --clean`
  - 14 tests passed; query-facade SSD snapshot and aggregate accounting remain
    intact.
- `SIMPLE_LIB=src bin/simple spipe-docgen test/01_unit/lib/nogc_sync_mut/database/sql_join_aggregate_offload_adapter_spec.spl --output doc/06_spec --no-index`
  - regenerated 1 complete doc with existing docgen warnings outside this lane
    and one short-doc warning.
- `SIMPLE_LIB=src bin/simple spipe-docgen test/01_unit/lib/nogc_sync_mut/database/pure_sql_offload_spec.spl --output doc/06_spec --no-index`
  - regenerated 1 complete doc after the validated grouped join aggregate
    scenario; remaining warning is the existing short-document warning.
- `sh scripts/check/check-proxy-live-socket-benchmark.shs`
  - `STATUS: PASS proxy live socket benchmark`; native-built
    `proxy_live_native_backend.spl` and `proxy_live_native_cached_proxy.spl`,
    then generated `native_simple_cached_proxy_http_50` in the live socket
    report and metrics table.
- `sh scripts/check/check-proxy-benchmark-report.shs`
  - `STATUS: PASS proxy benchmark report`; now gates
    `native_simple_cached_proxy_http_50` in addition to the deterministic proxy
    spec rows and Python reference live socket rows. The wrapper now parses
    both the report and metrics table and requires all three live rows to have
    50 iterations, nonzero bytes/RSS, expected upstream reuse/connect counts,
    and zero timeouts/errors. Latest native row:
    `native_simple_cached_proxy_http_50`, p50/p95/p99 `682/741/773us`,
    `upstream_reuse=49`, `upstream_connects=1`, `errors=0`, `timeouts=0`.
- `bin/simple check src/lib/nogc_async_mut/http_server/proxy.spl src/lib/nogc_async_mut/http_server/worker.spl src/lib/nogc_async_mut/http_server/__init__.spl test/01_unit/lib/nogc_async_mut/http_server/async_reverse_proxy_spec.spl`
  - passed after enabling chunked early proxy handoff with framed chunk
    forwarding, preserving `Transfer-Encoding: chunked` upstream instead of
    requiring a precomputed dechunked `Content-Length`.
- `SIMPLE_LIB=src bin/simple test test/01_unit/lib/nogc_async_mut/http_server/async_reverse_proxy_spec.spl --mode=interpreter --clean`
  - 74 tests passed, including split chunk-frame boundaries, split terminal
    chunks, malformed framing rejection, terminal-chunk trailing-byte rejection,
    and incomplete chunk staging-buffer budget enforcement.
- `SIMPLE_LIB=src bin/simple spipe-docgen test/01_unit/lib/nogc_async_mut/http_server/async_reverse_proxy_spec.spl --output doc/06_spec --no-index`
  - regenerated 1 complete doc with the existing short-document warning.
- `bin/simple check src/lib/nogc_sync_mut/db/dbfs_engine/offload_snapshot.spl src/lib/nogc_sync_mut/db/dbfs_engine/__init__.spl src/lib/nogc_sync_mut/database/storage_mode_offload.spl src/lib/nogc_sync_mut/database/query_offload.spl src/lib/nogc_sync_mut/database/__init__.spl test/02_integration/storage/dbfs/dbfs_ssd_offload_snapshot_spec.spl test/01_unit/lib/nogc_sync_mut/database/db_query_offload_spec.spl`
  - passed after adding DBFS-owned SSD scan row-id derivation and scan facades
    that no longer accept caller-provided CPU row IDs.
- `SIMPLE_LIB=src bin/simple test test/02_integration/storage/dbfs/dbfs_ssd_offload_snapshot_spec.spl --mode=interpreter --clean`
  - 7 tests passed, including current snapshot row-id derivation and stale
    snapshot empty-manifest behavior.
- `SIMPLE_LIB=src bin/simple test test/01_unit/lib/nogc_sync_mut/database/db_query_offload_spec.spl --mode=interpreter --clean`
  - 15 tests passed, including the no-caller-row-id SSD scan facade returning
    snapshot-derived row IDs.
- `SIMPLE_LIB=src bin/simple spipe-docgen test/02_integration/storage/dbfs/dbfs_ssd_offload_snapshot_spec.spl --output doc/06_spec --no-index`
  - regenerated 1 complete doc with existing docgen warnings outside this lane
    and one short-doc warning.
- `SIMPLE_LIB=src bin/simple spipe-docgen test/01_unit/lib/nogc_sync_mut/database/db_query_offload_spec.spl --output doc/06_spec --no-index`
  - regenerated 1 complete doc with existing docgen warnings outside this lane
    and one short-doc warning.
- `bin/simple check src/lib/nogc_sync_mut/db/dbfs_engine/offload_snapshot.spl src/lib/nogc_sync_mut/db/dbfs_engine/__init__.spl src/lib/nogc_sync_mut/database/storage_mode_offload.spl src/lib/nogc_sync_mut/database/query_offload.spl src/lib/nogc_sync_mut/database/__init__.spl test/02_integration/storage/dbfs/dbfs_ssd_offload_snapshot_spec.spl test/01_unit/lib/nogc_sync_mut/database/db_query_offload_spec.spl`
  - passed after adding DBFS SSD page-cursor scan materialization and validated
    materialized-scan query/storage facades.
- `SIMPLE_LIB=src bin/simple test test/02_integration/storage/dbfs/dbfs_ssd_offload_snapshot_spec.spl --mode=interpreter --clean`
  - 13 tests passed, including clean pager page-cursor row materialization,
    projected SSD materialized scan candidate match/mismatch validation, and
    missing page-cursor rejection. Runtime was 98161ms and the runner flagged
    the spec as a perf bug.
- `SIMPLE_LIB=src bin/simple test test/01_unit/lib/nogc_sync_mut/database/db_query_offload_spec.spl --mode=interpreter --clean`
  - 17 tests passed, including accepted and rejected GPU candidate row IDs
    compared against DBFS page-cursor materialized CPU rows.
- `SIMPLE_LIB=src bin/simple spipe-docgen test/02_integration/storage/dbfs/dbfs_ssd_offload_snapshot_spec.spl --output doc/06_spec --no-index`
  - regenerated 1 complete doc with existing docgen warnings outside this lane
    and one short-doc warning.
- `bin/simple check test/02_integration/storage/dbfs/dbfs_ssd_offload_snapshot_spec.spl`
  - passed after adding projected SSD materialized scan validation scenarios.
- `SIMPLE_LIB=src bin/simple test test/02_integration/storage/dbfs/dbfs_ssd_offload_snapshot_spec.spl --mode=interpreter --clean`
  - 13 tests passed; the new scenarios validate matching projected
    page-cursor row IDs through `db_storage_execute_ssd_materialized_scan_validated`
    and reject mismatched GPU candidates while preserving DBFS-owned row IDs.
- `SIMPLE_LIB=src bin/simple spipe-docgen test/02_integration/storage/dbfs/dbfs_ssd_offload_snapshot_spec.spl --output doc/06_spec --no-index`
  - regenerated the DBFS SSD offload snapshot manual with existing toolchain
    warnings and a short-doc warning.
- `SIMPLE_LIB=src bin/simple spipe-docgen test/01_unit/lib/nogc_sync_mut/database/db_query_offload_spec.spl --output doc/06_spec --no-index`
  - regenerated 1 complete doc with existing docgen warnings outside this lane
- `bin/simple check src/lib/nogc_sync_mut/database/core.spl test/01_unit/lib/nogc_sync_mut/database/storage_row_batch_offload_spec.spl src/lib/nogc_sync_mut/db/dbfs_engine/offload_snapshot.spl test/02_integration/storage/dbfs/dbfs_ssd_offload_snapshot_spec.spl`
  - passed after adding DBFS SSD payload-byte materialization and
    `SdnTable.storage_row_batch_with_ssd_snapshot_validated`.
- `bin/simple test test/01_unit/lib/nogc_sync_mut/database/storage_row_batch_offload_spec.spl`
  - 11 tests passed, including SSD table GPU candidate row match acceptance and
    mismatch fallback while preserving CPU-authoritative table row IDs.
- `SIMPLE_LIB=src bin/simple spipe-docgen test/01_unit/lib/nogc_sync_mut/database/storage_row_batch_offload_spec.spl --output doc/06_spec --no-index`
  - regenerated 1 complete manual doc with existing toolchain warnings and the
    pre-existing short-document warning.
- `bin/simple check src/lib/nogc_sync_mut/db/dbfs_engine/offload_snapshot.spl test/02_integration/storage/dbfs/dbfs_ssd_offload_snapshot_spec.spl`
  - passed after adding projected SSD row-value materialization.
- `SIMPLE_LIB=src bin/simple test test/02_integration/storage/dbfs/dbfs_ssd_offload_snapshot_spec.spl --mode=interpreter --clean`
  - 14 tests passed, including projected `id`/`amount` value materialization and
    fail-closed empty projected rows for bad projection/page-cursor paths.
    Runtime was 101700ms and the runner still flagged this spec as a perf bug.
- `SIMPLE_LIB=src bin/simple spipe-docgen test/02_integration/storage/dbfs/dbfs_ssd_offload_snapshot_spec.spl --output doc/06_spec --no-index`
  - regenerated 1 complete manual doc with existing toolchain warnings and the
    pre-existing short-document warning.
    and one short-doc warning.
- `bin/simple check src/lib/nogc_sync_mut/web_db_offload/contract.spl src/lib/nogc_sync_mut/web_db_offload/__init__.spl test/01_unit/lib/nogc_sync_mut/web_db_offload/gpu_web_db_offload_scheduler_spec.spl`
  - passed after adding reusable `GpuWdbCoarseBatchProfile` data-path profiles
    for pinned web payload batches, RAM GPU-resident DB batches, SSD staged GPU
    batches, NoSQL/vector index batches, and CPU-only proxy/control work.
- `bin/simple test test/01_unit/lib/nogc_sync_mut/web_db_offload/gpu_web_db_offload_scheduler_spec.spl --mode=interpreter`
  - 14 tests passed, including the coarse profile contract and GPU admission
    guard that refuses CPU-only proxy/control profiles even when GPU evidence
    is otherwise present.
- `bin/simple check src/lib/nogc_sync_mut/database/gpu_mode_plan.spl src/lib/nogc_sync_mut/database/__init__.spl test/01_unit/lib/nogc_sync_mut/database/gpu_mode_plan_spec.spl`
  - passed after adding `GpuWdbCoarseBatchProfile` to `DbGpuModePlan` so DB
    planners expose RAM GPU-resident, SSD staged, NoSQL index, and vector index
    data paths with CPU control/durability metadata.
- `bin/simple test test/01_unit/lib/nogc_sync_mut/database/gpu_mode_plan_spec.spl --mode=interpreter`
  - 5 tests passed, covering RAM-only GPU resident batches, stale SSD WAL CPU
    fallback, CPU-owned NoSQL metadata filtering, and vector index batch mode.
- `SIMPLE_LIB=src bin/simple spipe-docgen test/01_unit/lib/nogc_sync_mut/database/gpu_mode_plan_spec.spl --output doc/06_spec --no-index`
  - regenerated 1 complete doc with the existing short-document warning.
- `bin/simple check src/lib/nogc_sync_mut/database/storage_mode_offload.spl src/lib/nogc_sync_mut/database/__init__.spl test/01_unit/lib/nogc_sync_mut/database/storage_mode_offload_spec.spl`
  - passed after propagating `GpuWdbCoarseBatchProfile` through the
    DB-server-facing storage execution facade and validation wrappers.
- `bin/simple test test/01_unit/lib/nogc_sync_mut/database/storage_mode_offload_spec.spl --mode=interpreter`
  - 11 tests passed, covering RAM GPU-resident, SSD staged, NoSQL index, and
    vector index profile metadata on dispatch, fallback, and CPU-oracle
    validation paths.
- `SIMPLE_LIB=src bin/simple spipe-docgen test/01_unit/lib/nogc_sync_mut/database/storage_mode_offload_spec.spl --output doc/06_spec --no-index`
  - regenerated 1 complete doc with existing docgen warnings outside this lane
    and one short-doc warning.
- `bin/simple check src/lib/nogc_sync_mut/database/query_offload.spl src/lib/nogc_sync_mut/database/sql_join_aggregate_offload.spl src/lib/nogc_sync_mut/database/pure_sql/database_part2.spl test/01_unit/lib/nogc_sync_mut/database/db_query_offload_spec.spl test/01_unit/lib/nogc_sync_mut/database/sql_join_aggregate_offload_adapter_spec.spl test/01_unit/lib/nogc_sync_mut/database/pure_sql_offload_spec.spl`
  - passed after carrying `GpuWdbCoarseBatchProfile` through query fallback,
    scheduled/deferred query results, SQL join/aggregate validation wrappers,
    and Pure SQL authority marking.
- `bin/simple test test/01_unit/lib/nogc_sync_mut/database/db_query_offload_spec.spl --mode=interpreter`
  - 17 tests passed, including RAM, SSD, NoSQL, vector, scheduled, deferred,
    and aggregate profile metadata at the DB query facade boundary.
- `bin/simple test test/01_unit/lib/nogc_sync_mut/database/sql_join_aggregate_offload_adapter_spec.spl --mode=interpreter`
  - 5 tests passed, including RAM and SSD profile preservation through SQL
    join/aggregate dispatch, validation, and CPU fallback.
- `bin/simple test test/01_unit/lib/nogc_sync_mut/database/pure_sql_offload_spec.spl --mode=interpreter`
  - 11 tests passed, including Pure SQL scan/filter/project RAM dispatch,
    validated scan/filter/project candidate rows, no-hardware validated-scan
    fallback, RAM/stale-SSD profile metadata, CPU-authoritative paths, and
    validated GPU-candidate paths.
- `SIMPLE_LIB=src bin/simple spipe-docgen test/01_unit/lib/nogc_sync_mut/database/db_query_offload_spec.spl test/01_unit/lib/nogc_sync_mut/database/sql_join_aggregate_offload_adapter_spec.spl test/01_unit/lib/nogc_sync_mut/database/pure_sql_offload_spec.spl --output doc/06_spec --no-index`
  - regenerated 3 complete docs with existing docgen warnings outside this
    lane and short-doc warnings.
- `bin/simple check src/lib/nogc_sync_mut/database/pure_sql/database_part2.spl test/01_unit/lib/nogc_sync_mut/database/pure_sql_offload_spec.spl`
  - passed after adding Pure SQL filtered projection scan/filter/project
    coverage.
- `bin/simple test test/01_unit/lib/nogc_sync_mut/database/pure_sql_offload_spec.spl --mode=interpreter`
  - 11 tests passed, including `SELECT name FROM users WHERE uid > 1` routing
    to `DbStorageOffloadWorkload.ScanFilterProject`,
    `gpu_db_columnar_scan_batch`, validated `gpu-cpu-row-match` candidate
    metadata, and no-hardware validated-scan fallback.
- `SIMPLE_LIB=src bin/simple spipe-docgen test/01_unit/lib/nogc_sync_mut/database/pure_sql_offload_spec.spl --output doc/06_spec --no-index`
  - regenerated the Pure SQL offload manual with the existing short-doc
    warning.
- `bin/simple check src/lib/nogc_sync_mut/database/pure_sql/database_part2.spl src/lib/nogc_sync_mut/database/query_offload.spl src/lib/nogc_sync_mut/database/storage_mode_offload.spl test/01_unit/lib/nogc_sync_mut/database/pure_sql_offload_spec.spl`
  - passed after adding the strict native Pure SQL filtered projection
    replacement gate.
- `SIMPLE_LIB=src bin/simple test test/01_unit/lib/nogc_sync_mut/database/pure_sql_offload_spec.spl --mode=interpreter`
  - 14 tests passed, including production filtered projection row replacement
    only after native timing and CPU row-ID agreement, plus mismatch and
    perf-only rejection.
- `SIMPLE_LIB=src bin/simple spipe-docgen test/01_unit/lib/nogc_sync_mut/database/pure_sql_offload_spec.spl --output doc/06_spec --no-index`
  - regenerated 1 complete Pure SQL manual; remaining warnings are existing
    toolchain warnings and a short-doc warning.
- `bin/simple check src/lib/nogc_sync_mut/database/pure_sql/database_part2.spl test/01_unit/lib/nogc_sync_mut/database/pure_sql_offload_spec.spl`
  - passed after extending the engine-owned validated aggregate candidate path
    from grouped `COUNT(*)` to grouped `SUM(column)`.
- `SIMPLE_LIB=src bin/simple test test/01_unit/lib/nogc_sync_mut/database/pure_sql_offload_spec.spl --mode=interpreter --clean`
  - 17 tests passed, including grouped SUM CPU-oracle candidate validation with
    `gpu-cpu-row-match` and `result_source: gpu_candidate_validated`.
- `SIMPLE_LIB=src bin/simple spipe-docgen test/01_unit/lib/nogc_sync_mut/database/pure_sql_offload_spec.spl --output doc/06_spec --no-index`
  - regenerated 1 complete Pure SQL manual; remaining warnings are existing
    toolchain warnings and a short-doc warning.
- `bin/simple check src/lib/nogc_sync_mut/web_db_offload/web_route.spl src/lib/nogc_sync_mut/web_db_offload/web_profile.spl src/lib/nogc_sync_mut/web_framework/gpu_offload.spl src/lib/nogc_async_mut/web_framework/dispatcher.spl test/01_unit/lib/nogc_sync_mut/web_db_offload/web_route_gpu_offload_spec.spl test/01_unit/lib/nogc_sync_mut/web_db_offload/web_route_profile_spec.spl test/01_unit/lib/nogc_sync_mut/web_framework/gpu_offload_spec.spl test/01_unit/lib/nogc_async_mut/web_framework/dispatcher_spec.spl`
  - passed after adding `GpuWdbCoarseBatchProfile` to web route offload
    execution results so controller and dispatcher callers can distinguish
    pinned host payload batches from CPU-only proxy/control-plane work.
- `bin/simple test test/01_unit/lib/nogc_sync_mut/web_db_offload/web_route_gpu_offload_spec.spl --mode=interpreter`
  - 9 tests passed, including pinned-host profile metadata for inference,
    tiny-batch CPU fallback, deferred embedding work, and CPU-only proxy
    forwarding.
- `bin/simple test test/01_unit/lib/nogc_sync_mut/web_db_offload/web_route_profile_spec.spl --mode=interpreter`
  - 11 tests passed, including profile-level pinned-host payload metadata and
    CPU-only proxy forwarding through all-web profiles.
- `bin/simple test test/01_unit/lib/nogc_sync_mut/web_framework/gpu_offload_spec.spl --mode=interpreter`
  - 9 tests passed, including controller-facing pinned-host route metadata and
    CPU-only unconfigured action adoption.
- `bin/simple test test/01_unit/lib/nogc_async_mut/web_framework/dispatcher_spec.spl --mode=interpreter`
  - 3 tests passed, including async dispatcher adoption metadata for GPU-worthy
    rank routes and CPU-only health/control-plane routes.
- `SIMPLE_LIB=src bin/simple spipe-docgen test/01_unit/lib/nogc_sync_mut/web_db_offload/web_route_gpu_offload_spec.spl test/01_unit/lib/nogc_sync_mut/web_db_offload/web_route_profile_spec.spl test/01_unit/lib/nogc_sync_mut/web_framework/gpu_offload_spec.spl test/01_unit/lib/nogc_async_mut/web_framework/dispatcher_spec.spl --output doc/06_spec --no-index`
  - regenerated 4 complete docs with existing docgen warnings outside this
    lane and short-doc warnings.
- `bin/simple check src/lib/nogc_sync_mut/web_framework/gpu_offload.spl src/lib/nogc_sync_mut/web_framework/__init__.spl src/lib/nogc_async_mut/web_framework/dispatcher.spl test/01_unit/lib/nogc_sync_mut/web_framework/gpu_offload_spec.spl test/01_unit/lib/nogc_async_mut/web_framework/dispatcher_spec.spl`
  - passed after exposing validated web profile response replacement through
    framework route helpers and dispatcher adoption.
- `SIMPLE_LIB=src bin/simple test test/01_unit/lib/nogc_sync_mut/web_framework/gpu_offload_spec.spl --mode=interpreter`
  - 12 tests passed, including framework-level production response replacement
    only after native timing and CPU response agreement, plus mismatch and
    perf-only rejection.
- `SIMPLE_LIB=src bin/simple test test/01_unit/lib/nogc_async_mut/web_framework/dispatcher_spec.spl --mode=interpreter`
  - 7 tests passed, including matched validated dispatcher replacement and
    unconfigured route CPU ownership.
- `SIMPLE_LIB=src bin/simple spipe-docgen test/01_unit/lib/nogc_sync_mut/web_framework/gpu_offload_spec.spl test/01_unit/lib/nogc_async_mut/web_framework/dispatcher_spec.spl --output doc/06_spec --no-index`
  - regenerated 2 complete framework manuals; remaining warnings are existing
    toolchain warnings and short-doc warnings.
- `bin/simple check src/lib/nogc_sync_mut/web_db_offload/web_route.spl src/lib/nogc_sync_mut/web_db_offload/__init__.spl src/lib/nogc_sync_mut/web_db_offload/web_profile.spl src/lib/nogc_sync_mut/web_framework/gpu_offload.spl test/01_unit/lib/nogc_sync_mut/web_db_offload/web_route_gpu_offload_spec.spl test/01_unit/lib/nogc_sync_mut/web_db_offload/web_route_profile_spec.spl test/01_unit/lib/nogc_sync_mut/web_framework/gpu_offload_spec.spl`
  - passed after routing `web_gpu_route_offload_used_gpu` through
    `web_gpu_route_profile_allows_gpu`, so GPU evidence requires both a GPU
    queue decision and a non-CPU-only coarse profile.
- `bin/simple test test/01_unit/lib/nogc_sync_mut/web_db_offload/web_route_gpu_offload_spec.spl --mode=interpreter`
  - 9 tests passed, including direct guard coverage for GPU-worthy inference,
    tiny-batch CPU fallback, and CPU-only proxy forwarding.
- `bin/simple test test/01_unit/lib/nogc_sync_mut/web_db_offload/web_route_profile_spec.spl --mode=interpreter`
  - 11 tests passed, including profile-level guard coverage for inference,
    missing-target CPU fallback, and proxy forwarding.
- `bin/simple test test/01_unit/lib/nogc_sync_mut/web_framework/gpu_offload_spec.spl --mode=interpreter`
  - 9 tests passed, including controller-facing guard evidence for matched
    GPU-worthy actions and unconfigured control-plane fallback.
- `SIMPLE_LIB=src bin/simple spipe-docgen test/01_unit/lib/nogc_sync_mut/web_db_offload/web_route_gpu_offload_spec.spl test/01_unit/lib/nogc_sync_mut/web_db_offload/web_route_profile_spec.spl test/01_unit/lib/nogc_sync_mut/web_framework/gpu_offload_spec.spl --output doc/06_spec --no-index`
  - regenerated 3 complete docs with existing docgen warnings outside this
    lane and short-doc warnings.
- `bin/simple check src/lib/nogc_sync_mut/database/storage_mode_offload.spl src/lib/nogc_sync_mut/database/__init__.spl test/01_unit/lib/nogc_sync_mut/database/storage_mode_offload_spec.spl test/01_unit/lib/nogc_sync_mut/database/db_query_offload_spec.spl test/01_unit/lib/nogc_sync_mut/database/pure_sql_offload_spec.spl`
  - passed after routing `db_storage_offload_used_gpu` through
    `db_storage_profile_allows_gpu`, so DB GPU evidence now requires both a
    dispatch flag and an eligible coarse profile.
- `bin/simple test test/01_unit/lib/nogc_sync_mut/database/storage_mode_offload_spec.spl --mode=interpreter`
  - 11 tests passed, including direct guard coverage for RAM, SSD, NoSQL,
    vector, stale-generation, and CPU-oracle mismatch paths.
- `bin/simple test test/01_unit/lib/nogc_sync_mut/database/db_query_offload_spec.spl --mode=interpreter`
  - 17 tests passed, including query-facade guard coverage for dispatch,
    fallback, deferred, and document/vector paths.
- `bin/simple test test/01_unit/lib/nogc_sync_mut/database/pure_sql_offload_spec.spl --mode=interpreter`
  - 8 tests passed, including Pure SQL guard evidence for CPU-authoritative,
    validated GPU-candidate, and stale-SSD aggregate observations.
- `SIMPLE_LIB=src bin/simple spipe-docgen test/01_unit/lib/nogc_sync_mut/database/storage_mode_offload_spec.spl test/01_unit/lib/nogc_sync_mut/database/db_query_offload_spec.spl test/01_unit/lib/nogc_sync_mut/database/pure_sql_offload_spec.spl --output doc/06_spec --no-index`
  - regenerated 3 complete docs with existing docgen warnings outside this
    lane and short-doc warnings.
- `bin/simple check src/lib/nogc_sync_mut/database/db_offload.spl src/lib/nogc_sync_mut/database/nosql_offload.spl src/lib/nogc_sync_mut/database/vector/search_offload.spl src/lib/nogc_sync_mut/database/__init__.spl src/lib/nogc_sync_mut/database/vector/__init__.spl test/01_unit/lib/nogc_sync_mut/database/db_gpu_batch_offload_spec.spl test/01_unit/lib/nogc_sync_mut/database/nosql_document_offload_spec.spl test/01_unit/lib/nogc_sync_mut/database/vector/vector_search_offload_adapter_spec.spl`
  - passed after adding profile-aware guard helpers to the lower RAM/SSD,
    NoSQL, and vector offload adapters.
- `bin/simple test test/01_unit/lib/nogc_sync_mut/database/db_gpu_batch_offload_spec.spl --mode=interpreter`
  - 5 tests passed, including RAM/SSD batch profile guard evidence.
- `bin/simple test test/01_unit/lib/nogc_sync_mut/database/nosql_document_offload_spec.spl --mode=interpreter`
  - 7 tests passed, including NoSQL index profile guard evidence for dispatch,
    missing target, metadata CPU-ownership rejection, stale generation, and
    durable collection reload paths.
- `bin/simple test test/01_unit/lib/nogc_sync_mut/database/vector/vector_search_offload_adapter_spec.spl --mode=interpreter`
  - 3 tests passed after fixing vector execution to honor the planner decision
    before submitting to a registered GPU target. GPU-owned metadata filtering
    now stays on CPU/reject evidence instead of reaching GPU submission.
- `SIMPLE_LIB=src bin/simple spipe-docgen test/01_unit/lib/nogc_sync_mut/database/db_gpu_batch_offload_spec.spl test/01_unit/lib/nogc_sync_mut/database/nosql_document_offload_spec.spl test/01_unit/lib/nogc_sync_mut/database/vector/vector_search_offload_adapter_spec.spl --output doc/06_spec --no-index`
  - regenerated 3 complete docs with existing docgen warnings outside this
    lane and short-doc warnings.
- `bin/simple check src/lib/nogc_sync_mut/database/offload_profile.spl src/lib/nogc_sync_mut/database/__init__.spl test/01_unit/lib/nogc_sync_mut/database/db_offload_profile_spec.spl`
  - passed after adding DB profile facade helpers
    `db_offload_profile_execution_allows_gpu` and
    `db_offload_profile_execution_used_gpu`.
- `bin/simple test test/01_unit/lib/nogc_sync_mut/database/db_offload_profile_spec.spl --mode=interpreter`
  - 11 tests passed, covering profile-level GPU evidence guards and data-path
    metadata for RAM-heavy, NoSQL, vector, CPU-only, deferred, and immediate
    dispatch paths.
- `SIMPLE_LIB=src bin/simple spipe-docgen test/01_unit/lib/nogc_sync_mut/database/db_offload_profile_spec.spl --output doc/06_spec --no-index`
  - regenerated 1 complete doc with existing docgen warnings outside this lane
    and one short-doc warning.
- `bin/simple check src/lib/nogc_sync_mut/web_db_offload/web_profile.spl src/lib/nogc_sync_mut/web_db_offload/__init__.spl test/01_unit/lib/nogc_sync_mut/web_db_offload/web_route_profile_spec.spl`
  - passed after adding web profile facade helpers
    `web_gpu_profile_execution_allows_gpu` and
    `web_gpu_profile_execution_used_gpu`.
- `bin/simple test test/01_unit/lib/nogc_sync_mut/web_db_offload/web_route_profile_spec.spl --mode=interpreter`
  - 11 tests passed, covering profile-level GPU evidence guards for inference,
    missing-target fallback, CPU-only profiles, deferred batches, immediate
    dispatch, and CPU-only proxy forwarding.
- `SIMPLE_LIB=src bin/simple spipe-docgen test/01_unit/lib/nogc_sync_mut/web_db_offload/web_route_profile_spec.spl --output doc/06_spec --no-index`
  - regenerated 1 complete doc with existing docgen warnings outside this lane
    and one short-doc warning.
- `bin/simple check src/lib/nogc_async_mut/web_framework/dispatcher.spl src/lib/nogc_async_mut/web_framework/app.spl test/01_unit/lib/nogc_async_mut/web_framework/dispatcher_spec.spl`
  - dispatcher and spec passed after adding `configure_gpu_profile` to
    `AppDispatcher` and `WebApp`.
- `bin/simple test test/01_unit/lib/nogc_async_mut/web_framework/dispatcher_spec.spl --mode=interpreter`
  - 5 tests passed, covering reusable web profile adoption for rank dispatch
    and CPU-only profile fallback through the production dispatcher path.
- `SIMPLE_LIB=src bin/simple spipe-docgen test/01_unit/lib/nogc_async_mut/web_framework/dispatcher_spec.spl --output doc/06_spec --no-index`
  - regenerated 1 complete doc with existing docgen warnings outside this lane
    and one short-doc warning.
- `bin/simple check src/lib/nogc_async_mut/web_framework/app.spl src/lib/nogc_async_mut/web_framework/dispatcher.spl test/01_unit/lib/nogc_async_mut/web_framework/dispatcher_spec.spl`
  - passed after moving `WebApp` config file loading from the sync runtime
    family import to the async `std.fs.read_file` facade, removing the
    runtime-family warning on the web framework entrypoint.
- `bin/simple check src/lib/nogc_async_mut/web_framework/router.spl src/lib/nogc_async_mut/web_framework/app.spl`
  - passed after moving route-file loading from the sync runtime family import
    to the async `std.fs.read_file` facade, removing the remaining
    web-framework file-loading runtime-family warning.
- `bin/simple test test/01_unit/lib/nogc_async_mut/web_framework/web_framework_facade_spec.spl --mode=interpreter`
  - passed, covering the async web framework facade after the config and route
    loader boundary cleanup.
- `bin/simple check src/lib/nogc_async_mut/http_server/proxy.spl test/01_unit/lib/nogc_async_mut/http_server/async_reverse_proxy_spec.spl`
  - passed after tightening tunnel request serialization to drop `Keep-Alive`,
    `TE`, and `Trailer` while preserving the required WebSocket `Upgrade`
    setup headers.
- `bin/simple test test/01_unit/lib/nogc_async_mut/http_server/async_reverse_proxy_spec.spl --mode=interpreter`
  - 74 tests passed, covering the async reverse-proxy policy layer including the
    strengthened tunnel hop-by-hop header filtering.
- `SIMPLE_LIB=src bin/simple spipe-docgen test/01_unit/lib/nogc_async_mut/http_server/async_reverse_proxy_spec.spl --output doc/06_spec --no-index`
  - regenerated the async reverse-proxy manual with the updated tunnel header
    assertions; docgen still reports existing toolchain warnings and the known
    short-doc warning for this spec.
- `bin/simple check src/lib/nogc_sync_mut/web_db_offload/library.spl src/lib/nogc_sync_mut/web_db_offload/web_profile.spl src/lib/nogc_sync_mut/web_db_offload/__init__.spl src/lib/nogc_sync_mut/database/offload_profile.spl src/lib/nogc_sync_mut/database/__init__.spl test/01_unit/lib/nogc_sync_mut/web_db_offload/gpu_web_db_offload_library_spec.spl test/01_unit/lib/nogc_sync_mut/web_db_offload/web_route_profile_spec.spl test/01_unit/lib/nogc_sync_mut/database/db_offload_profile_spec.spl`
  - passed after adding reusable GPU library generation freshness helpers and
    profile flush APIs that accept an expected target generation instead of a
    loose freshness boolean.
- `bin/simple test test/01_unit/lib/nogc_sync_mut/web_db_offload/gpu_web_db_offload_library_spec.spl --mode=interpreter`
  - 5 tests passed, covering registered target admission, stale generation CPU
    fallback, empty-backend snapshots, and CPU-only proxy forwarding.
- `bin/simple test test/01_unit/lib/nogc_sync_mut/web_db_offload/web_route_profile_spec.spl --mode=interpreter`
  - 12 tests passed, including stale web target generation fallback through the
    reusable profile flush API.
- `bin/simple test test/01_unit/lib/nogc_sync_mut/database/db_offload_profile_spec.spl --mode=interpreter`
  - 12 tests passed, including stale DB target generation fallback through the
    reusable profile flush API.
- `SIMPLE_LIB=src bin/simple spipe-docgen test/01_unit/lib/nogc_sync_mut/web_db_offload/gpu_web_db_offload_library_spec.spl test/01_unit/lib/nogc_sync_mut/web_db_offload/web_route_profile_spec.spl test/01_unit/lib/nogc_sync_mut/database/db_offload_profile_spec.spl --output doc/06_spec --no-index`
  - regenerated 3 complete docs; remaining warnings are short-doc/toolchain
    warnings, with the library spec now carrying requirements, plan, design,
    research, and examples metadata.
- `bin/simple check src/lib/nogc_sync_mut/web_db_offload/web_route.spl src/lib/nogc_sync_mut/web_db_offload/web_profile.spl src/lib/nogc_sync_mut/web_db_offload/__init__.spl test/01_unit/lib/nogc_sync_mut/web_db_offload/web_route_gpu_offload_spec.spl test/01_unit/lib/nogc_sync_mut/web_db_offload/web_route_profile_spec.spl`
  - passed after routing scheduled web-route dispatch through the reusable
    registry-generation snapshot and submit helpers.
- `bin/simple test test/01_unit/lib/nogc_sync_mut/web_db_offload/web_route_gpu_offload_spec.spl --mode=interpreter`
  - 10 tests passed, including direct route-level stale target generation
    fallback before GPU evidence can be recorded.
- `bin/simple test test/01_unit/lib/nogc_sync_mut/web_db_offload/web_route_profile_spec.spl --mode=interpreter`
  - 13 tests passed, including profile-level stale scheduled target generation
    fallback with `stale-generation` evidence.
- `SIMPLE_LIB=src bin/simple spipe-docgen test/01_unit/lib/nogc_sync_mut/web_db_offload/web_route_gpu_offload_spec.spl test/01_unit/lib/nogc_sync_mut/web_db_offload/web_route_profile_spec.spl --output doc/06_spec --no-index`
  - regenerated 2 complete docs; remaining warnings are existing toolchain
    warnings and short-doc warnings.
- `bin/simple check src/lib/nogc_sync_mut/database/db_offload.spl src/lib/nogc_sync_mut/database/__init__.spl test/01_unit/lib/nogc_sync_mut/database/db_gpu_batch_offload_spec.spl`
  - passed after adding `db_gpu_batch_offload_execute_for_generation`, which
    binds RAM/SSD DB batch GPU dispatch to an expected registry generation
    while preserving WAL/data freshness checks.
- `bin/simple test test/01_unit/lib/nogc_sync_mut/database/db_gpu_batch_offload_spec.spl --mode=interpreter`
  - 6 tests passed, including registry-generation mismatch fallback distinct
    from stale SSD WAL generation fallback.
- `SIMPLE_LIB=src bin/simple spipe-docgen test/01_unit/lib/nogc_sync_mut/database/db_gpu_batch_offload_spec.spl --output doc/06_spec --no-index`
  - regenerated 1 complete DB batch offload manual; remaining warnings are
    existing toolchain warnings and a short-doc warning.
- `bin/simple check src/lib/nogc_sync_mut/database/nosql_offload.spl src/lib/nogc_sync_mut/database/__init__.spl test/01_unit/lib/nogc_sync_mut/database/nosql_document_offload_spec.spl`
  - passed after adding `nosql_document_offload_execute_for_generation`, which
    binds document-filter GPU dispatch to an expected registry generation while
    preserving CPU-owned metadata filtering and collection generation freshness.
- `bin/simple test test/01_unit/lib/nogc_sync_mut/database/nosql_document_offload_spec.spl --mode=interpreter`
  - 8 tests passed, including registry-generation mismatch fallback distinct
    from stale document collection generation fallback.
- `SIMPLE_LIB=src bin/simple spipe-docgen test/01_unit/lib/nogc_sync_mut/database/nosql_document_offload_spec.spl --output doc/06_spec --no-index`
  - regenerated 1 complete NoSQL document offload manual; remaining warnings
    are existing toolchain warnings and a short-doc warning.
- `bin/simple check src/lib/nogc_sync_mut/database/vector/search_offload.spl src/lib/nogc_sync_mut/database/vector/__init__.spl src/lib/nogc_sync_mut/database/__init__.spl test/01_unit/lib/nogc_sync_mut/database/vector/vector_search_offload_adapter_spec.spl`
  - passed after adding `vector_search_offload_execute_for_generation`, which
    binds vector-search GPU dispatch to an expected registry generation while
    preserving CPU-owned metadata filtering and authoritative CPU results.
- `bin/simple test test/01_unit/lib/nogc_sync_mut/database/vector/vector_search_offload_adapter_spec.spl --mode=interpreter`
  - 4 tests passed, including registry-generation mismatch fallback distinct
    from missing GPU target and CPU-owned metadata-filter rejection.
- `SIMPLE_LIB=src bin/simple spipe-docgen test/01_unit/lib/nogc_sync_mut/database/vector/vector_search_offload_adapter_spec.spl --output doc/06_spec --no-index`
  - regenerated 1 complete vector search offload manual; remaining warnings are
    existing toolchain warnings and a short-doc warning.
- `bin/simple check src/lib/nogc_async_mut/http_server/proxy.spl test/01_unit/lib/nogc_async_mut/http_server/async_reverse_proxy_spec.spl`
  - passed after teaching the async proxy response state machine that 1xx,
    `204`, and `304` upstream responses have no body and can complete at header
    completion instead of waiting for upstream EOF.
- `bin/simple test test/01_unit/lib/nogc_async_mut/http_server/async_reverse_proxy_spec.spl --mode=interpreter`
  - 76 tests passed, including no-body status completion and suppression of
    accidental upstream body bytes for `304` responses.
- `SIMPLE_LIB=src bin/simple spipe-docgen test/01_unit/lib/nogc_async_mut/http_server/async_reverse_proxy_spec.spl --output doc/06_spec --no-index`
  - regenerated 1 complete async reverse-proxy manual; remaining warnings are
    existing toolchain warnings and a short-doc warning.
- `bin/simple check src/lib/nogc_async_mut/http_server/proxy.spl test/01_unit/lib/nogc_async_mut/http_server/async_reverse_proxy_spec.spl`
  - passed after switching request upgrade detection and upstream reuse
    `Connection: close` detection to comma-token parsing instead of substring
    matching.
- `bin/simple test test/01_unit/lib/nogc_async_mut/http_server/async_reverse_proxy_spec.spl --mode=interpreter`
  - 78 tests passed, including upgrade/close token parsing regressions for
    mixed-case comma tokens and non-token substrings such as `xupgrade` and
    `enclose`.
- `SIMPLE_LIB=src bin/simple spipe-docgen test/01_unit/lib/nogc_async_mut/http_server/async_reverse_proxy_spec.spl --output doc/06_spec --no-index`
  - regenerated 1 complete async reverse-proxy manual; remaining warnings are
    existing toolchain warnings and a short-doc warning.
- `bin/simple check src/lib/nogc_async_mut/http_server/proxy.spl test/01_unit/lib/nogc_async_mut/http_server/async_reverse_proxy_spec.spl`
  - passed after switching request and response `Transfer-Encoding: chunked`
    detection to comma-token parsing instead of substring matching.
- `bin/simple test test/01_unit/lib/nogc_async_mut/http_server/async_reverse_proxy_spec.spl --mode=interpreter`
  - 80 tests passed, including request and upstream response chunked transfer
    token regressions for mixed-case comma tokens and `xchunked` substrings.
- `SIMPLE_LIB=src bin/simple spipe-docgen test/01_unit/lib/nogc_async_mut/http_server/async_reverse_proxy_spec.spl --output doc/06_spec --no-index`
  - regenerated 1 complete async reverse-proxy manual; remaining warnings are
    existing toolchain warnings and a short-doc warning.
- `bin/simple check src/lib/nogc_sync_mut/database/storage_mode_offload.spl src/lib/nogc_sync_mut/database/query_offload.spl src/lib/nogc_sync_mut/database/sql_join_aggregate_offload.spl src/lib/nogc_sync_mut/database/pure_sql/database_part2.spl src/lib/nogc_sync_mut/database/offload_profile.spl src/lib/nogc_sync_mut/web_db_offload/web_profile.spl test/01_unit/lib/nogc_sync_mut/database/db_offload_profile_spec.spl test/01_unit/lib/nogc_sync_mut/web_db_offload/web_route_profile_spec.spl`
  - passed after adding profile-advancing execution wrappers and carrying full
    `GpuWdbQueueState` through `DbStorageOffloadExecution`.
- `bin/simple test test/01_unit/lib/nogc_sync_mut/database/db_offload_profile_spec.spl --mode=interpreter`
  - 13 tests passed, including sequential `db_offload_profile_execute_advancing`
    queue-accounting evidence for submitted, completed, and GPU-hit counters.
- `bin/simple test test/01_unit/lib/nogc_sync_mut/web_db_offload/web_route_profile_spec.spl --mode=interpreter`
  - 14 tests passed, including sequential `web_gpu_profile_execute_advancing`
    queue-accounting evidence while preserving CPU-authoritative responses.
- `SIMPLE_LIB=src bin/simple spipe-docgen test/01_unit/lib/nogc_sync_mut/database/db_offload_profile_spec.spl test/01_unit/lib/nogc_sync_mut/web_db_offload/web_route_profile_spec.spl --output doc/06_spec --no-index`
  - regenerated 2 complete profile manuals; remaining warnings are existing
    toolchain warnings and short-doc warnings.
- `bin/simple check src/lib/nogc_sync_mut/database/offload_profile.spl src/lib/nogc_sync_mut/web_db_offload/web_profile.spl test/01_unit/lib/nogc_sync_mut/database/db_offload_profile_spec.spl test/01_unit/lib/nogc_sync_mut/web_db_offload/web_route_profile_spec.spl`
  - passed after adding profile-advancing accumulator flush wrappers for DB and
    web profile APIs.
- `bin/simple test test/01_unit/lib/nogc_sync_mut/database/db_offload_profile_spec.spl --mode=interpreter`
  - 14 tests passed, including `db_offload_profile_flush_accumulator_current_advancing`
    evidence that a flushed GPU batch advances submitted/GPU-hit counters and
    retains queue-depth pressure before completion.
- `bin/simple test test/01_unit/lib/nogc_sync_mut/web_db_offload/web_route_profile_spec.spl --mode=interpreter`
  - 15 tests passed, including `web_gpu_profile_flush_accumulator_current_advancing`
    evidence for the same queued-batch profile state update on web payload
    batches.
- `SIMPLE_LIB=src bin/simple spipe-docgen test/01_unit/lib/nogc_sync_mut/database/db_offload_profile_spec.spl test/01_unit/lib/nogc_sync_mut/web_db_offload/web_route_profile_spec.spl --output doc/06_spec --no-index`
  - regenerated 2 complete profile manuals; remaining warnings are existing
    toolchain warnings and short-doc warnings.
- `bin/simple check src/lib/nogc_sync_mut/database/offload_profile.spl src/lib/nogc_sync_mut/web_db_offload/web_profile.spl test/01_unit/lib/nogc_sync_mut/database/db_offload_profile_spec.spl test/01_unit/lib/nogc_sync_mut/web_db_offload/web_route_profile_spec.spl`
  - passed after adding profile-level completion helpers for flushed GPU queue
    submissions.
- `bin/simple test test/01_unit/lib/nogc_sync_mut/database/db_offload_profile_spec.spl --mode=interpreter`
  - 15 tests passed, including two-step accumulated DB flush completion evidence
    that releases queue-depth pressure and increments completed GPU work.
- `bin/simple test test/01_unit/lib/nogc_sync_mut/web_db_offload/web_route_profile_spec.spl --mode=interpreter`
  - 16 tests passed, including matching web profile completion evidence after
    two deferred batches are flushed to a registered GPU target.
- `SIMPLE_LIB=src bin/simple spipe-docgen test/01_unit/lib/nogc_sync_mut/database/db_offload_profile_spec.spl test/01_unit/lib/nogc_sync_mut/web_db_offload/web_route_profile_spec.spl --output doc/06_spec --no-index`
  - regenerated 2 complete profile manuals; remaining warnings are existing
    toolchain warnings and short-doc warnings.
- `bin/simple check src/lib/nogc_sync_mut/database/__init__.spl src/lib/nogc_sync_mut/web_db_offload/__init__.spl test/01_unit/lib/nogc_sync_mut/database/db_offload_profile_spec.spl test/01_unit/lib/nogc_sync_mut/web_db_offload/web_route_profile_spec.spl`
  - passed after adding the new stateful web profile helpers to the
    `std.web_db_offload` package facade and normalizing the DB offload-profile
    export list to explicit `export use` syntax.
- `bin/simple test test/01_unit/lib/nogc_sync_mut/web_db_offload/web_route_profile_spec.spl --mode=interpreter`
  - 17 tests passed, including root-package import evidence for
    `web_gpu_profile_execute_advancing` through `std.web_db_offload`.
- `bin/simple test test/01_unit/lib/nogc_sync_mut/database/db_offload_profile_spec.spl --mode=interpreter`
  - 15 tests passed for the owning `std.database.offload_profile` module; a
    direct `std.database.{...}` import is not currently how this package facade
    resolves offload profile symbols.
- `SIMPLE_LIB=src bin/simple spipe-docgen test/01_unit/lib/nogc_sync_mut/database/db_offload_profile_spec.spl test/01_unit/lib/nogc_sync_mut/web_db_offload/web_route_profile_spec.spl --output doc/06_spec --no-index`
  - regenerated 2 complete profile manuals; remaining warnings are existing
    toolchain warnings and short-doc warnings.
- `bin/simple check src/lib/nogc_async_mut/http_server/proxy.spl test/01_unit/lib/nogc_async_mut/http_server/async_reverse_proxy_spec.spl`
  - passed after adding fail-closed request framing checks for ambiguous
    `Content-Length` plus `Transfer-Encoding` and unsupported transfer codings.
- `bin/simple test test/01_unit/lib/nogc_async_mut/http_server/async_reverse_proxy_spec.spl --mode=interpreter`
  - 82 tests passed, including buffered and streaming proxy plan rejection for
    conflicting body framing and unsupported non-chunked transfer encoding.
- `SIMPLE_LIB=src bin/simple spipe-docgen test/01_unit/lib/nogc_async_mut/http_server/async_reverse_proxy_spec.spl --output doc/06_spec --no-index`
  - regenerated 1 complete async reverse-proxy manual; remaining warnings are
    existing toolchain warnings and a short-doc warning.
- `bin/simple check src/lib/nogc_async_mut/http_server/proxy.spl test/01_unit/lib/nogc_async_mut/http_server/async_reverse_proxy_spec.spl`
  - passed after adding upstream response framing validation for ambiguous
    `Content-Length` plus `Transfer-Encoding` and unsupported transfer codings.
- `bin/simple test test/01_unit/lib/nogc_async_mut/http_server/async_reverse_proxy_spec.spl --mode=interpreter`
  - 84 tests passed, including response validation and state-machine rejection
    before client send for conflicting upstream response framing.
- `SIMPLE_LIB=src bin/simple spipe-docgen test/01_unit/lib/nogc_async_mut/http_server/async_reverse_proxy_spec.spl --output doc/06_spec --no-index`
  - regenerated 1 complete async reverse-proxy manual; remaining warnings are
    existing toolchain warnings and a short-doc warning.
- `bin/simple check src/lib/nogc_async_mut/http_server/proxy.spl test/01_unit/lib/nogc_async_mut/http_server/async_reverse_proxy_spec.spl`
  - passed after adding fail-closed invalid/conflicting `Content-Length`
    validation on client request and upstream response proxy framing.
- `bin/simple test test/01_unit/lib/nogc_async_mut/http_server/async_reverse_proxy_spec.spl --mode=interpreter`
  - 86 tests passed, including duplicate matching `Content-Length` acceptance
    and mismatched or invalid `Content-Length` rejection before forwarding.
- `SIMPLE_LIB=src bin/simple spipe-docgen test/01_unit/lib/nogc_async_mut/http_server/async_reverse_proxy_spec.spl --output doc/06_spec --no-index`
  - regenerated 1 complete async reverse-proxy manual; remaining warnings are
    existing toolchain warnings and a short-doc warning.
- `bin/simple check src/lib/nogc_async_mut/http_server/proxy.spl test/01_unit/lib/nogc_async_mut/http_server/async_reverse_proxy_spec.spl`
  - passed after tightening proxy transfer-coding validation so mixed codings
    such as `gzip, chunked` are rejected instead of being treated as plain
    chunked streams.
- `bin/simple test test/01_unit/lib/nogc_async_mut/http_server/async_reverse_proxy_spec.spl --mode=interpreter`
  - 86 tests passed, including request and upstream response evidence that the
    `chunked` token can be detected while mixed transfer codings still fail
    closed before forwarding or client send.
- `SIMPLE_LIB=src bin/simple spipe-docgen test/01_unit/lib/nogc_async_mut/http_server/async_reverse_proxy_spec.spl --output doc/06_spec --no-index`
  - regenerated 1 complete async reverse-proxy manual; remaining warnings are
    existing toolchain warnings and a short-doc warning.
- `bin/simple check src/lib/nogc_sync_mut/web_db_offload/device_backend.spl src/lib/nogc_sync_mut/web_db_offload/__init__.spl test/01_unit/lib/nogc_sync_mut/web_db_offload/gpu_web_db_offload_device_backend_spec.spl`
  - passed after adding the strict native device-backend runner boundary.
- `SIMPLE_LIB=src bin/simple test test/01_unit/lib/nogc_sync_mut/web_db_offload/gpu_web_db_offload_device_backend_spec.spl --mode=interpreter`
  - 3 tests passed, covering measured native columnar scan evidence,
    perf/mock backend rejection for production claims, and stale-generation CPU
    fallback before dispatch.
- `SIMPLE_LIB=src bin/simple spipe-docgen test/01_unit/lib/nogc_sync_mut/web_db_offload/gpu_web_db_offload_device_backend_spec.spl --output doc/06_spec --no-index`
  - regenerated 1 complete device-backend manual; remaining warnings are
    existing toolchain warnings and a short-doc warning.
- `bin/simple check src/lib/nogc_sync_mut/web_db_offload/device_backend.spl src/lib/nogc_sync_mut/database/offload_profile.spl src/lib/nogc_sync_mut/database/__init__.spl test/01_unit/lib/nogc_sync_mut/database/db_offload_profile_spec.spl`
  - passed after wiring DB profile requests through strict device-backend
    evidence.
- `SIMPLE_LIB=src bin/simple test test/01_unit/lib/nogc_sync_mut/database/db_offload_profile_spec.spl --mode=interpreter`
  - 17 tests passed, including RAM-heavy row scan production device evidence and
    perf/mock backend rejection while preserving CPU-authoritative output.
- `SIMPLE_LIB=src bin/simple spipe-docgen test/01_unit/lib/nogc_sync_mut/database/db_offload_profile_spec.spl --output doc/06_spec --no-index`
  - regenerated 1 complete DB offload profile manual; remaining warnings are
    existing toolchain warnings and a short-doc warning.
- `bin/simple check src/lib/nogc_sync_mut/database/db_offload.spl src/lib/nogc_sync_mut/database/__init__.spl test/01_unit/lib/nogc_sync_mut/database/db_gpu_batch_offload_spec.spl`
  - passed after adding direct DB batch device-backend execution.
- `SIMPLE_LIB=src bin/simple test test/01_unit/lib/nogc_sync_mut/database/db_gpu_batch_offload_spec.spl --mode=interpreter`
  - 8 tests passed, including native device evidence for RAM scan/filter/project
    batches and perf-only backend rejection while preserving CPU row IDs.
- `SIMPLE_LIB=src bin/simple test test/01_unit/lib/nogc_sync_mut/web_db_offload/gpu_web_db_offload_device_backend_spec.spl --mode=interpreter`
  - 3 tests passed after preserving non-native backend generation while
    exposing no device targets, so perf-only rejection reports
    `gpu-unavailable` instead of stale generation.
- `SIMPLE_LIB=src bin/simple spipe-docgen test/01_unit/lib/nogc_sync_mut/database/db_gpu_batch_offload_spec.spl --output doc/06_spec --no-index`
  - regenerated 1 complete DB batch offload manual; remaining warnings are
    existing toolchain warnings and a short-doc warning.
- `bin/simple check src/lib/nogc_sync_mut/web_db_offload/web_profile.spl src/lib/nogc_sync_mut/web_db_offload/__init__.spl test/01_unit/lib/nogc_sync_mut/web_db_offload/web_route_profile_spec.spl`
  - passed after adding strict native device-backend execution to reusable web
    GPU profiles and exporting the API through `std.web_db_offload`.
- `SIMPLE_LIB=src bin/simple test test/01_unit/lib/nogc_sync_mut/web_db_offload/web_route_profile_spec.spl --mode=interpreter`
  - 19 tests passed, including native measured web inference evidence,
    CPU-authoritative response preservation, and stale target generation
    fallback before production GPU claims.
- `SIMPLE_LIB=src bin/simple spipe-docgen test/01_unit/lib/nogc_sync_mut/web_db_offload/web_route_profile_spec.spl --output doc/06_spec --no-index`
  - regenerated 1 complete web route profile manual; remaining warnings are
    existing toolchain warnings and a short-doc warning.
- `bin/simple check src/lib/nogc_sync_mut/web_db_offload/web_profile.spl src/lib/nogc_sync_mut/web_db_offload/__init__.spl test/01_unit/lib/nogc_sync_mut/web_db_offload/web_route_profile_spec.spl`
  - passed after adding validated web profile response replacement through the
    strict native device backend.
- `SIMPLE_LIB=src bin/simple test test/01_unit/lib/nogc_sync_mut/web_db_offload/web_route_profile_spec.spl --mode=interpreter`
  - 22 tests passed, including production web inference response replacement
    only after native timing and CPU response agreement, plus mismatch and
    perf-only rejection.
- `SIMPLE_LIB=src bin/simple spipe-docgen test/01_unit/lib/nogc_sync_mut/web_db_offload/web_route_profile_spec.spl --output doc/06_spec --no-index`
  - regenerated 1 complete web route profile manual; remaining warnings are
    existing toolchain warnings and a short-doc warning.
- `bin/simple check src/lib/nogc_sync_mut/web_db_offload/web_profile.spl src/lib/nogc_sync_mut/web_db_offload/__init__.spl test/01_unit/lib/nogc_sync_mut/web_db_offload/web_route_profile_spec.spl`
  - passed after adding transform-route coverage for the existing generic web
    profile strict response replacement boundary.
- `SIMPLE_LIB=src bin/simple test test/01_unit/lib/nogc_sync_mut/web_db_offload/web_route_profile_spec.spl --mode=interpreter --clean`
  - 25 tests passed, including `WebGpuRouteKind.Transform` response
    replacement only after measured native timing and CPU response agreement,
    plus mismatch and perf-only rejection.
- `SIMPLE_LIB=src bin/simple spipe-docgen test/01_unit/lib/nogc_sync_mut/web_db_offload/web_route_profile_spec.spl --output doc/06_spec --no-index`
  - regenerated 1 complete web route profile manual; remaining warning is the
    existing short-doc warning.
- `bin/simple check src/lib/nogc_sync_mut/database/nosql_offload.spl src/lib/nogc_sync_mut/database/__init__.spl test/01_unit/lib/nogc_sync_mut/database/nosql_document_offload_spec.spl`
  - passed after adding an SSD-backed NoSQL document collection wrapper with
    durable-generation freshness before GPU document-filter dispatch.
- `SIMPLE_LIB=src bin/simple test test/01_unit/lib/nogc_sync_mut/database/nosql_document_offload_spec.spl --mode=interpreter`
  - 10 tests passed, including saved SSD NoSQL metadata offload and unsaved
    durable-state fallback to CPU before GPU evidence.
- `SIMPLE_LIB=src bin/simple spipe-docgen test/01_unit/lib/nogc_sync_mut/database/nosql_document_offload_spec.spl --output doc/06_spec --no-index`
  - regenerated 1 complete NoSQL document offload manual; remaining warnings
    are existing toolchain warnings and a short-doc warning.
- `bin/simple check src/lib/nogc_sync_mut/database/storage_mode_offload.spl src/lib/nogc_sync_mut/database/__init__.spl test/01_unit/lib/nogc_sync_mut/database/storage_mode_offload_spec.spl`
  - passed after bridging SSD-backed NoSQL document collections through the
    DB storage-mode facade.
- `SIMPLE_LIB=src bin/simple test test/01_unit/lib/nogc_sync_mut/database/storage_mode_offload_spec.spl --mode=interpreter`
  - 13 tests passed, including saved SSD NoSQL document offload through the
    storage facade and unsaved durable-state fallback to CPU.
- `SIMPLE_LIB=src bin/simple spipe-docgen test/01_unit/lib/nogc_sync_mut/database/storage_mode_offload_spec.spl --output doc/06_spec --no-index`
  - regenerated 1 complete storage-mode offload manual; remaining warnings are
    existing toolchain warnings and a short-doc warning.
- `bin/simple check src/lib/nogc_sync_mut/database/query.spl src/lib/nogc_sync_mut/database/query_offload.spl src/lib/nogc_sync_mut/database/__init__.spl test/01_unit/lib/nogc_sync_mut/database/query_builder_offload_spec.spl test/01_unit/lib/nogc_sync_mut/database/db_query_offload_spec.spl`
  - passed after adding query-facade and QueryBuilder measured-native row
    replacement gates.
- `SIMPLE_LIB=src bin/simple test test/01_unit/lib/nogc_sync_mut/database/db_query_offload_spec.spl --mode=interpreter`
  - 24 tests passed, including production query row replacement only after
    measured native evidence and CPU row-ID agreement, plus mismatch and
    perf-only rejection.
- `SIMPLE_LIB=src bin/simple test test/01_unit/lib/nogc_sync_mut/database/query_builder_offload_spec.spl --mode=interpreter`
  - 5 tests passed, including QueryBuilder RAM-only scan/filter/project row
    replacement through measured native columnar-scan candidates.
- `SIMPLE_LIB=src bin/simple spipe-docgen test/01_unit/lib/nogc_sync_mut/database/db_query_offload_spec.spl test/01_unit/lib/nogc_sync_mut/database/query_builder_offload_spec.spl --output doc/06_spec --no-index`
  - regenerated 2 complete query offload manuals; remaining warnings are
    existing toolchain warnings and short-doc warnings.
- `bin/simple check src/lib/nogc_sync_mut/database/query.spl src/lib/nogc_sync_mut/database/__init__.spl test/01_unit/lib/nogc_sync_mut/database/query_builder_offload_spec.spl`
  - passed after adding QueryBuilder SSD materialized projection consumption.
- `SIMPLE_LIB=src bin/simple test test/01_unit/lib/nogc_sync_mut/database/query_builder_offload_spec.spl --mode=interpreter --clean`
  - 7 tests passed, including returning projected SSD `SdnRow` values after
    `gpu-cpu-row-match` and falling back to CPU rows on candidate mismatch.
- `SIMPLE_LIB=src bin/simple spipe-docgen test/01_unit/lib/nogc_sync_mut/database/query_builder_offload_spec.spl --output doc/06_spec --no-index`
  - regenerated 1 complete QueryBuilder manual; remaining warnings are existing
    toolchain warnings and a short-doc warning.
- `bin/simple check src/lib/nogc_sync_mut/database/query.spl src/lib/nogc_sync_mut/database/__init__.spl test/01_unit/lib/nogc_sync_mut/database/query_builder_offload_spec.spl`
  - passed after adding live QueryBuilder filtered SUM offload accounting.
- `SIMPLE_LIB=src bin/simple test test/01_unit/lib/nogc_sync_mut/database/query_builder_offload_spec.spl --mode=interpreter --clean`
  - 8 tests passed, including `sum_i64_with_storage_offload("score")` returning
    CPU-authoritative `90` and routing through `gpu_db_join_aggregate_batch`.
- `SIMPLE_LIB=src bin/simple spipe-docgen test/01_unit/lib/nogc_sync_mut/database/query_builder_offload_spec.spl --output doc/06_spec --no-index`
  - regenerated 1 complete QueryBuilder manual; remaining warnings are existing
    toolchain warnings and a short-doc warning.
- `bin/simple check src/lib/nogc_sync_mut/database/query.spl src/lib/nogc_sync_mut/database/__init__.spl test/01_unit/lib/nogc_sync_mut/database/query_builder_offload_spec.spl`
  - passed after adding QueryBuilder SSD projected SUM consumption.
- `SIMPLE_LIB=src bin/simple test test/01_unit/lib/nogc_sync_mut/database/query_builder_offload_spec.spl --mode=interpreter --clean`
  - 10 tests passed, including `sum_i64_with_ssd_materialized_projection`
    consuming validated projected SSD numeric values and falling back to CPU SUM
    on candidate row-ID mismatch.
- `SIMPLE_LIB=src bin/simple spipe-docgen test/01_unit/lib/nogc_sync_mut/database/query_builder_offload_spec.spl --output doc/06_spec --no-index`
  - regenerated 1 complete QueryBuilder manual; remaining warnings are existing
    toolchain warnings and a short-doc warning.
- `bin/simple check src/lib/nogc_sync_mut/database/query.spl src/lib/nogc_sync_mut/database/__init__.spl test/01_unit/lib/nogc_sync_mut/database/query_builder_offload_spec.spl`
  - passed after adding QueryBuilder SSD projected COUNT consumption.
- `SIMPLE_LIB=src bin/simple test test/01_unit/lib/nogc_sync_mut/database/query_builder_offload_spec.spl --mode=interpreter --clean`
  - 12 tests passed, including `count_with_ssd_materialized_projection`
    consuming validated projected SSD row IDs and falling back to CPU COUNT on
    candidate row-ID mismatch.
- `SIMPLE_LIB=src bin/simple spipe-docgen test/01_unit/lib/nogc_sync_mut/database/query_builder_offload_spec.spl --output doc/06_spec --no-index`
  - regenerated 1 complete QueryBuilder manual; remaining warnings are existing
    toolchain warnings and a short-doc warning.
- `bin/simple check src/lib/nogc_sync_mut/database/query.spl src/lib/nogc_sync_mut/database/__init__.spl test/01_unit/lib/nogc_sync_mut/database/query_builder_offload_spec.spl`
  - passed after naming the QueryBuilder SSD projected COUNT operator helper.
- `SIMPLE_LIB=src bin/simple test test/01_unit/lib/nogc_sync_mut/database/query_builder_offload_spec.spl --mode=interpreter --clean`
  - 12 tests passed, including the explicit SSD projected COUNT helper path
    and CPU fallback on candidate row-ID mismatch.
- `SIMPLE_LIB=src bin/simple spipe-docgen test/01_unit/lib/nogc_sync_mut/database/query_builder_offload_spec.spl --output doc/06_spec --no-index`
  - regenerated 1 complete QueryBuilder manual; remaining warnings are existing
    toolchain warnings and a short-doc warning.
- `bin/simple check src/lib/nogc_sync_mut/database/query_offload.spl src/lib/nogc_sync_mut/database/__init__.spl test/01_unit/lib/nogc_sync_mut/database/db_query_offload_spec.spl`
  - passed after adding a DB query facade helper for SSD-backed NoSQL document
    collections.
- `SIMPLE_LIB=src bin/simple test test/01_unit/lib/nogc_sync_mut/database/db_query_offload_spec.spl --mode=interpreter`
  - 19 tests passed, including saved SSD NoSQL document query offload and
    unsaved durable-state fallback to CPU at the query boundary.
- `SIMPLE_LIB=src bin/simple spipe-docgen test/01_unit/lib/nogc_sync_mut/database/db_query_offload_spec.spl --output doc/06_spec --no-index`
  - regenerated 1 complete DB query offload manual; remaining warnings are
    existing toolchain warnings and a short-doc warning.
- `bin/simple check src/lib/nogc_sync_mut/database/storage_mode_offload.spl src/lib/nogc_sync_mut/database/core.spl src/lib/nogc_sync_mut/database/__init__.spl test/01_unit/lib/nogc_sync_mut/database/storage_row_batch_offload_spec.spl`
  - passed after adding storage facade and `SdnTable` native device-backend row
    batch execution.
- `SIMPLE_LIB=src bin/simple test test/01_unit/lib/nogc_sync_mut/database/storage_row_batch_offload_spec.spl --mode=interpreter`
  - 9 tests passed, including native device evidence for table-owned
    scan/filter/project row batches with CPU-authoritative valid row IDs.
- `SIMPLE_LIB=src bin/simple spipe-docgen test/01_unit/lib/nogc_sync_mut/database/storage_row_batch_offload_spec.spl --output doc/06_spec --no-index`
  - regenerated 1 complete storage row batch manual; remaining warnings are
    existing toolchain warnings and a short-doc warning.
- `bin/simple check src/lib/nogc_sync_mut/database/storage_mode_offload.spl src/lib/nogc_sync_mut/database/__init__.spl test/01_unit/lib/nogc_sync_mut/database/storage_mode_offload_spec.spl`
  - passed after adding the measured-native row replacement gate to the storage
    facade.
- `SIMPLE_LIB=src bin/simple test test/01_unit/lib/nogc_sync_mut/database/storage_mode_offload_spec.spl --mode=interpreter`
  - 16 tests passed, including production device row replacement only when
    measured native evidence and GPU row candidates match CPU rows.
- `SIMPLE_LIB=src bin/simple spipe-docgen test/01_unit/lib/nogc_sync_mut/database/storage_mode_offload_spec.spl --output doc/06_spec --no-index`
  - regenerated 1 complete storage-mode offload manual; remaining warnings are
    existing toolchain warnings and a short-doc warning.
- `bin/simple check src/lib/nogc_sync_mut/database/offload_profile.spl src/lib/nogc_sync_mut/database/__init__.spl test/01_unit/lib/nogc_sync_mut/database/db_offload_profile_spec.spl`
  - passed after adding profile-level SSD-backed NoSQL document execution.
- `SIMPLE_LIB=src bin/simple test test/01_unit/lib/nogc_sync_mut/database/db_offload_profile_spec.spl --mode=interpreter`
  - 19 tests passed, including saved SSD NoSQL document offload through the
    reusable NoSQL profile and unsaved durable-state CPU fallback.
- `SIMPLE_LIB=src bin/simple spipe-docgen test/01_unit/lib/nogc_sync_mut/database/db_offload_profile_spec.spl --output doc/06_spec --no-index`
  - regenerated 1 complete DB offload profile manual; remaining warnings are
    existing toolchain warnings and a short-doc warning.
- `bin/simple check src/lib/nogc_sync_mut/database/nosql_offload.spl src/lib/nogc_sync_mut/database/offload_profile.spl src/lib/nogc_sync_mut/database/__init__.spl test/01_unit/lib/nogc_sync_mut/database/db_offload_profile_spec.spl`
  - passed after fixing `NoSqlSsdDocumentCollection.save` to mutate durable
    generation state explicitly and adding strict native device evidence for
    profile-level SSD NoSQL document filters.
- `SIMPLE_LIB=src bin/simple test test/01_unit/lib/nogc_sync_mut/database/db_offload_profile_spec.spl --mode=interpreter`
  - 22 tests passed, including measured native SSD NoSQL document evidence,
    unsaved durable-state fallback, and perf-only backend rejection.
- `SIMPLE_LIB=src bin/simple spipe-docgen test/01_unit/lib/nogc_sync_mut/database/db_offload_profile_spec.spl --output doc/06_spec --no-index`
  - regenerated 1 complete DB offload profile manual; remaining warnings are
    existing toolchain warnings and a short-doc warning.
- `bin/simple check src/lib/nogc_sync_mut/database/storage_mode_offload.spl src/lib/nogc_sync_mut/database/nosql_offload.spl src/lib/nogc_sync_mut/database/__init__.spl test/01_unit/lib/nogc_sync_mut/database/storage_mode_offload_spec.spl`
  - passed after adding a measured-native SSD NoSQL document replacement gate
    at the storage facade.
- `SIMPLE_LIB=src bin/simple test test/01_unit/lib/nogc_sync_mut/database/storage_mode_offload_spec.spl --mode=interpreter`
  - 19 tests passed, including production document ID replacement only after
    native timing and CPU-oracle agreement, plus mismatch and perf-only
    rejection.
- `SIMPLE_LIB=src bin/simple spipe-docgen test/01_unit/lib/nogc_sync_mut/database/storage_mode_offload_spec.spl --output doc/06_spec --no-index`
  - regenerated 1 complete storage-mode offload manual; remaining warnings are
    existing toolchain warnings and a short-doc warning.
- `bin/simple check src/lib/nogc_sync_mut/database/storage_mode_offload.spl src/lib/nogc_sync_mut/database/__init__.spl test/01_unit/lib/nogc_sync_mut/database/storage_mode_offload_spec.spl`
  - passed after adding a measured-native SSD materialized scan replacement
    gate at the storage facade.
- `SIMPLE_LIB=src bin/simple test test/01_unit/lib/nogc_sync_mut/database/storage_mode_offload_spec.spl --mode=interpreter --clean`
  - 24 tests passed, including production SSD materialized row replacement
    only after native timing and CPU-oracle row-ID agreement, plus mismatch and
    perf-only rejection.
- `SIMPLE_LIB=src bin/simple spipe-docgen test/01_unit/lib/nogc_sync_mut/database/storage_mode_offload_spec.spl --output doc/06_spec --no-index`
  - regenerated 1 complete storage-mode offload manual; remaining warnings are
    existing toolchain warnings and a short-doc warning.
- `bin/simple check src/lib/nogc_sync_mut/database/query_offload.spl src/lib/nogc_sync_mut/database/__init__.spl test/01_unit/lib/nogc_sync_mut/database/db_query_offload_spec.spl`
  - passed after exposing measured-native SSD materialized scan replacement
    through the DB query facade.
- `SIMPLE_LIB=src bin/simple test test/01_unit/lib/nogc_sync_mut/database/db_query_offload_spec.spl --mode=interpreter --clean`
  - 29 tests passed, including query-level production SSD materialized row
    replacement only after native timing and CPU-oracle row-ID agreement, plus
    mismatch and perf-only rejection.
- `SIMPLE_LIB=src bin/simple spipe-docgen test/01_unit/lib/nogc_sync_mut/database/db_query_offload_spec.spl --output doc/06_spec --no-index`
  - regenerated 1 complete DB query offload manual; remaining warnings are
    existing toolchain warnings and a short-doc warning.
- `bin/simple check src/lib/nogc_sync_mut/database/offload_profile.spl src/lib/nogc_sync_mut/database/__init__.spl test/01_unit/lib/nogc_sync_mut/database/db_offload_profile_spec.spl`
  - passed after exposing measured-native SSD materialized scan replacement
    through DB offload profiles.
- `SIMPLE_LIB=src bin/simple test test/01_unit/lib/nogc_sync_mut/database/db_offload_profile_spec.spl --mode=interpreter --clean`
  - 25 tests passed, including profile-level production SSD materialized row
    replacement only after native timing and CPU-oracle row-ID agreement, plus
    mismatch and perf-only rejection.
- `SIMPLE_LIB=src bin/simple spipe-docgen test/01_unit/lib/nogc_sync_mut/database/db_offload_profile_spec.spl --output doc/06_spec --no-index`
  - regenerated 1 complete DB offload profile manual; remaining warnings are
    existing toolchain warnings and a short-doc warning.
- `bin/simple check src/lib/nogc_sync_mut/database/offload_profile.spl src/lib/nogc_sync_mut/database/storage_mode_offload.spl src/lib/nogc_sync_mut/database/__init__.spl test/01_unit/lib/nogc_sync_mut/database/db_offload_profile_spec.spl test/01_unit/lib/nogc_sync_mut/database/storage_mode_offload_spec.spl`
  - passed after exposing RAM NoSQL document-filter measured-native
    replacement through the storage facade and reusable NoSQL profile.
- `SIMPLE_LIB=src bin/simple test test/01_unit/lib/nogc_sync_mut/database/storage_mode_offload_spec.spl --mode=interpreter --clean`
  - 26 tests passed, including storage-level RAM document replacement only
    after measured native timing and CPU-oracle document-ID agreement.
- `SIMPLE_LIB=src bin/simple test test/01_unit/lib/nogc_sync_mut/database/db_offload_profile_spec.spl --mode=interpreter --clean`
  - 27 tests passed, including profile-level RAM document replacement and
    mismatch fallback through `db_offload_profile_execute_documents_device`.
- `SIMPLE_LIB=src bin/simple spipe-docgen test/01_unit/lib/nogc_sync_mut/database/storage_mode_offload_spec.spl test/01_unit/lib/nogc_sync_mut/database/db_offload_profile_spec.spl --output doc/06_spec --no-index`
  - regenerated 2 complete storage/profile manuals; remaining warnings are
    existing short-doc warnings.
- `bin/simple check src/lib/nogc_sync_mut/database/core.spl src/lib/nogc_sync_mut/database/__init__.spl test/01_unit/lib/nogc_sync_mut/database/storage_row_batch_offload_spec.spl`
  - passed after adding an `SdnTable` SSD materialized row handoff that returns
    projected SSD rows only when materialized row IDs, table CPU-valid row IDs,
    and GPU candidate row IDs agree.
- `SIMPLE_LIB=src bin/simple test test/01_unit/lib/nogc_sync_mut/database/storage_row_batch_offload_spec.spl --mode=interpreter --clean`
  - 13 tests passed, including projected SSD table-row materialization and CPU
    table-row fallback on candidate mismatch.
- `SIMPLE_LIB=src bin/simple spipe-docgen test/01_unit/lib/nogc_sync_mut/database/storage_row_batch_offload_spec.spl --output doc/06_spec --no-index`
  - regenerated 1 complete storage row batch manual; remaining warnings are
    existing toolchain warnings and a short-doc warning.
- `bin/simple check src/lib/nogc_sync_mut/database/core.spl test/01_unit/lib/nogc_sync_mut/database/storage_row_batch_offload_spec.spl`
  - passed after adding an `SdnTable` measured-native SSD materialized row
    replacement gate that returns projected SSD rows only when native timing,
    production device evidence, materialized row IDs, table CPU-valid row IDs,
    and GPU candidate row IDs agree.
- `SIMPLE_LIB=src bin/simple test test/01_unit/lib/nogc_sync_mut/database/storage_row_batch_offload_spec.spl --mode=interpreter --clean --sequential`
  - 15 tests passed, including native SSD materialized table-row replacement
    and CPU table-row fallback on candidate mismatch.
- `SIMPLE_LIB=src bin/simple spipe-docgen test/01_unit/lib/nogc_sync_mut/database/storage_row_batch_offload_spec.spl --output doc/06_spec --no-index`
  - regenerated 1 complete storage row batch manual; remaining warnings are
    existing toolchain warnings and a short-doc warning.
- `bin/simple check src/lib/nogc_sync_mut/database/query_offload.spl src/lib/nogc_sync_mut/database/offload_profile.spl src/lib/nogc_sync_mut/database/__init__.spl test/01_unit/lib/nogc_sync_mut/database/db_query_offload_spec.spl test/01_unit/lib/nogc_sync_mut/database/db_offload_profile_spec.spl`
  - passed after exposing measured-native SSD NoSQL document replacement
    through the query and profile layers.
- `SIMPLE_LIB=src bin/simple test test/01_unit/lib/nogc_sync_mut/database/db_query_offload_spec.spl --mode=interpreter`
  - 24 tests passed, including query-level production document replacement and
    mismatch fallback.
- `SIMPLE_LIB=src bin/simple test test/01_unit/lib/nogc_sync_mut/database/db_offload_profile_spec.spl --mode=interpreter`
  - 22 tests passed, including profile-level validated SSD NoSQL document
    replacement through the shared query gate.
- `SIMPLE_LIB=src bin/simple spipe-docgen test/01_unit/lib/nogc_sync_mut/database/db_query_offload_spec.spl test/01_unit/lib/nogc_sync_mut/database/db_offload_profile_spec.spl --output doc/06_spec --no-index`
  - regenerated 2 complete manuals; remaining warnings are existing toolchain
    warnings and short-doc warnings.
- `bin/simple check src/lib/nogc_sync_mut/database/vector/search_offload.spl src/lib/nogc_sync_mut/database/vector/__init__.spl src/lib/nogc_sync_mut/database/storage_mode_offload.spl src/lib/nogc_sync_mut/database/query_offload.spl src/lib/nogc_sync_mut/database/__init__.spl test/01_unit/lib/nogc_sync_mut/database/vector/vector_search_offload_adapter_spec.spl test/01_unit/lib/nogc_sync_mut/database/storage_mode_offload_spec.spl test/01_unit/lib/nogc_sync_mut/database/db_query_offload_spec.spl`
  - passed after adding vector-search CPU-oracle candidate validation through
    the vector adapter, storage facade, and query facade.
- `SIMPLE_LIB=src bin/simple test test/01_unit/lib/nogc_sync_mut/database/vector/vector_search_offload_adapter_spec.spl --mode=interpreter`
  - 6 tests passed, including matching vector candidate replacement and
    mismatched candidate CPU fallback.
- `SIMPLE_LIB=src bin/simple test test/01_unit/lib/nogc_sync_mut/database/storage_mode_offload_spec.spl --mode=interpreter`
  - 21 tests passed, including storage-level vector candidate validation.
- `SIMPLE_LIB=src bin/simple test test/01_unit/lib/nogc_sync_mut/database/db_query_offload_spec.spl --mode=interpreter`
  - 26 tests passed, including query-level vector candidate validation.
- `SIMPLE_LIB=src bin/simple spipe-docgen test/01_unit/lib/nogc_sync_mut/database/vector/vector_search_offload_adapter_spec.spl test/01_unit/lib/nogc_sync_mut/database/storage_mode_offload_spec.spl test/01_unit/lib/nogc_sync_mut/database/db_query_offload_spec.spl --output doc/06_spec --no-index`
  - regenerated 3 complete manuals; remaining warnings are existing toolchain
    warnings and short-doc warnings.
- `bin/simple check src/lib/nogc_sync_mut/database/vector/search_offload.spl src/lib/nogc_sync_mut/database/vector/store.spl src/lib/nogc_sync_mut/database/vector/__init__.spl src/lib/nogc_sync_mut/database/__init__.spl test/01_unit/lib/nogc_sync_mut/database/vector/vector_search_offload_adapter_spec.spl test/01_unit/lib/nogc_sync_mut/database/vector/vector_store_search_offload_spec.spl`
  - passed after adding the measured-native vector replacement gate and live
    vector-store wrapper.
- `SIMPLE_LIB=src bin/simple test test/01_unit/lib/nogc_sync_mut/database/vector/vector_search_offload_adapter_spec.spl --mode=interpreter`
  - 9 tests passed, including production vector result replacement only after
    native timing and CPU-oracle result-ID agreement, plus mismatch and
    perf-only rejection.
- `SIMPLE_LIB=src bin/simple test test/01_unit/lib/nogc_sync_mut/database/vector/vector_store_search_offload_spec.spl --mode=interpreter`
  - 7 tests passed, including live vector-store search replacement through
    measured native vector candidates.
- `SIMPLE_LIB=src bin/simple spipe-docgen test/01_unit/lib/nogc_sync_mut/database/vector/vector_search_offload_adapter_spec.spl test/01_unit/lib/nogc_sync_mut/database/vector/vector_store_search_offload_spec.spl --output doc/06_spec --no-index`
  - regenerated 2 complete vector manuals; remaining warnings are existing
    toolchain warnings and short-doc warnings.
- `bin/simple check src/lib/nogc_sync_mut/database/sql_join_aggregate_offload.spl src/lib/nogc_sync_mut/database/__init__.spl test/01_unit/lib/nogc_sync_mut/database/sql_join_aggregate_offload_adapter_spec.spl`
  - passed after adding strict measured-device validation for SQL
    join/aggregate offload.
- `SIMPLE_LIB=src bin/simple test test/01_unit/lib/nogc_sync_mut/database/sql_join_aggregate_offload_adapter_spec.spl --mode=interpreter`
  - 8 tests passed, including production join/aggregate replacement only after
    native device timing, join/aggregate target selection, row-ID agreement,
    and SQL row agreement; mismatch and perf-only backends remain CPU
    authoritative.
- `SIMPLE_LIB=src bin/simple spipe-docgen test/01_unit/lib/nogc_sync_mut/database/sql_join_aggregate_offload_adapter_spec.spl --output doc/06_spec --no-index`
  - regenerated 1 complete SQL join/aggregate manual; remaining warnings are
    existing toolchain warnings and a short-doc warning.
- `bin/simple check test/01_unit/lib/nogc_sync_mut/database/pure_sql_offload_spec.spl`
  - passed after adding Pure SQL grouped SUM production replacement evidence
    that accepts measured-native candidates only after grouped SQL rows match
    the CPU authority, with mismatch fallback.
- `SIMPLE_LIB=src bin/simple test test/01_unit/lib/nogc_sync_mut/database/pure_sql_offload_spec.spl --mode=interpreter --clean`
  - 19 tests passed, including grouped SUM measured-native replacement and
    CPU-authoritative fallback on native row mismatch.
- `SIMPLE_LIB=src bin/simple spipe-docgen test/01_unit/lib/nogc_sync_mut/database/pure_sql_offload_spec.spl --output doc/06_spec --no-index`
  - regenerated 1 complete Pure SQL offload manual; remaining warnings are
    existing toolchain warnings and a short-doc warning.
- `bin/simple check src/lib/nogc_sync_mut/database/pure_sql/database_part2.spl test/01_unit/lib/nogc_sync_mut/database/pure_sql_offload_spec.spl`
  - passed after adding Pure SQL grouped MAX measured-native replacement
    evidence, preserving strict CPU-oracle row agreement before native row
    adoption.
- `SIMPLE_LIB=src bin/simple test test/01_unit/lib/nogc_sync_mut/database/pure_sql_offload_spec.spl --mode=interpreter --clean --sequential`
  - 24 tests passed, including grouped SUM/AVG/MIN/MAX measured-native
    replacement and CPU-authoritative fallback on native row mismatch.
- `SIMPLE_LIB=src bin/simple spipe-docgen test/01_unit/lib/nogc_sync_mut/database/pure_sql_offload_spec.spl --output doc/06_spec --no-index`
  - regenerated 1 complete Pure SQL offload manual; remaining warnings are
    existing toolchain warnings and a short-doc warning.
- `bin/simple check src/lib/nogc_sync_mut/database/query.spl src/lib/nogc_sync_mut/database/__init__.spl test/01_unit/lib/nogc_sync_mut/database/query_builder_offload_spec.spl`
  - passed after adding QueryBuilder COUNT and numeric SUM measured-native
    aggregate replacement wrappers plus public exports.
- `SIMPLE_LIB=src bin/simple test test/01_unit/lib/nogc_sync_mut/database/query_builder_offload_spec.spl --mode=interpreter --clean`
  - 16 tests passed, including QueryBuilder COUNT/SUM production replacement,
    scalar mismatch fallback, and perf-only native evidence rejection.
- `SIMPLE_LIB=src bin/simple spipe-docgen test/01_unit/lib/nogc_sync_mut/database/query_builder_offload_spec.spl --output doc/06_spec --no-index`
  - regenerated 1 complete QueryBuilder offload manual; remaining warnings are
    existing toolchain warnings and a short-doc warning.
- `bin/simple check src/lib/nogc_sync_mut/database/query.spl src/lib/nogc_sync_mut/database/__init__.spl test/01_unit/lib/nogc_sync_mut/database/query_builder_offload_spec.spl`
  - passed after adding QueryBuilder SSD materialized COUNT/SUM measured-native
    aggregate replacement wrappers plus public exports.
- `SIMPLE_LIB=src bin/simple test test/01_unit/lib/nogc_sync_mut/database/query_builder_offload_spec.spl --mode=interpreter --clean`
  - 18 tests passed, including SSD materialized COUNT replacement after native
    timing and materialized row agreement, plus SSD SUM mismatch fallback.
- `SIMPLE_LIB=src bin/simple spipe-docgen test/01_unit/lib/nogc_sync_mut/database/query_builder_offload_spec.spl --output doc/06_spec --no-index`
  - regenerated 1 complete QueryBuilder offload manual; remaining warnings are
    existing toolchain warnings and a short-doc warning.
- `bin/simple check src/lib/nogc_sync_mut/database/query.spl test/01_unit/lib/nogc_sync_mut/database/query_builder_offload_spec.spl`
  - passed after adding QueryBuilder SSD materialized MIN/MAX measured-native
    aggregate replacement wrappers plus public exports.
- `SIMPLE_LIB=src bin/simple test test/01_unit/lib/nogc_sync_mut/database/query_builder_offload_spec.spl --mode=interpreter --clean --sequential`
  - 24 tests passed, including SSD materialized MIN replacement after native
    timing and materialized row agreement, plus SSD MAX mismatch fallback.
- `SIMPLE_LIB=src bin/simple spipe-docgen test/01_unit/lib/nogc_sync_mut/database/query_builder_offload_spec.spl --output doc/06_spec --no-index`
  - regenerated 1 complete QueryBuilder offload manual; remaining warnings are
    existing toolchain warnings and a short-doc warning.
- `bin/simple check src/lib/nogc_sync_mut/database/query.spl test/01_unit/lib/nogc_sync_mut/database/query_builder_offload_spec.spl`
  - passed after adding QueryBuilder filtered AVG join/aggregate accounting
    and measured-native AVG replacement with scalar mismatch fallback.
- `SIMPLE_LIB=src bin/simple test test/01_unit/lib/nogc_sync_mut/database/query_builder_offload_spec.spl --mode=interpreter --clean --sequential`
  - 27 tests passed, including AVG storage offload accounting, production
    AVG replacement after native timing and row agreement, and AVG mismatch
    fallback.
- `SIMPLE_LIB=src bin/simple spipe-docgen test/01_unit/lib/nogc_sync_mut/database/query_builder_offload_spec.spl --output doc/06_spec --no-index`
  - regenerated 1 complete QueryBuilder offload manual; remaining warnings are
    existing toolchain warnings and a short-doc warning.
- `bin/simple check src/lib/nogc_sync_mut/database/query.spl src/lib/nogc_sync_mut/database/__init__.spl test/01_unit/lib/nogc_sync_mut/database/query_builder_offload_spec.spl`
  - passed after adding QueryBuilder SSD materialized AVG projected aggregate
    validation, measured-native AVG replacement, scalar mismatch fallback, and
    public wrapper/export parity.
- `SIMPLE_LIB=src bin/simple test test/01_unit/lib/nogc_sync_mut/database/query_builder_offload_spec.spl --mode=interpreter --clean --sequential`
  - 30 tests passed, including SSD projected AVG validation, native SSD AVG
    replacement after materialized row agreement, and SSD AVG mismatch fallback.
- `SIMPLE_LIB=src bin/simple spipe-docgen test/01_unit/lib/nogc_sync_mut/database/query_builder_offload_spec.spl --output doc/06_spec --no-index`
  - regenerated 1 complete QueryBuilder offload manual; remaining warnings are
    existing toolchain warnings and a short-doc warning.
- `bin/simple check src/lib/nogc_sync_mut/database/query.spl test/01_unit/lib/nogc_sync_mut/database/query_builder_offload_spec.spl`
  - passed after adding explicit QueryBuilder SSD materialized MAX
    measured-native replacement evidence through the existing validated API.
- `SIMPLE_LIB=src bin/simple test test/01_unit/lib/nogc_sync_mut/database/query_builder_offload_spec.spl --mode=interpreter --clean --sequential`
  - 31 tests passed, including SSD projected COUNT/AVG/MIN/MAX replacement
    after native timing and materialized row agreement, plus SSD SUM/AVG/MAX
    mismatch fallback.
- `SIMPLE_LIB=src bin/simple spipe-docgen test/01_unit/lib/nogc_sync_mut/database/query_builder_offload_spec.spl --output doc/06_spec --no-index`
  - regenerated 1 complete QueryBuilder offload manual; remaining warnings are
    existing toolchain warnings and a short-doc warning.
- `sh scripts/check/check-gpu-web-db-offload-benchmark-report.shs`
  - passed with 5 benchmark examples and regenerated the GPU web/DB benchmark
    manual/report/table. The report now proves measured CUDA contract rows for
    vector search, columnar scan, join/aggregate, NoSQL document-filter, and
    web inference shapes plus the production-facing validated web response row.
- `bin/simple check test/05_perf/web_db_offload/gpu_web_db_offload_bench_spec.spl test/05_perf/web_db_offload/gpu_web_db_offload_web_transform_cuda_measured_driver.spl`
  - passed after adding the transform measured CUDA row validator and the
    independent web-transform CUDA driver.
- `sh scripts/check/check-gpu-web-db-offload-benchmark-report.shs`
  - `STATUS: PASS gpu web/db offload benchmark report`; regenerated the
    GPU web/DB benchmark manual/report/table and added
    `web_transform_cuda_measured | cuda | web_transform_8x2048_response_match |
    gpu_web_transform_batch | device_time_us=182 | native-device-measured`.
    A direct `bin/simple` interpreter run of the perf spec still reports the
    pre-existing `rt_host_gpu_queue_last_device_time_us` extern gap; the
    canonical wrapper passes with the repo native Simple binary.
- `bin/simple check test/05_perf/web_db_offload/gpu_web_db_offload_bench_spec.spl test/05_perf/web_db_offload/gpu_web_db_offload_web_embedding_cuda_measured_driver.spl test/05_perf/web_db_offload/gpu_web_db_offload_web_rank_cuda_measured_driver.spl`
  - passed after adding embedding/rank measured CUDA row validators and the
    independent web-embedding and web-rank CUDA drivers.
- `sh scripts/check/check-gpu-web-db-offload-benchmark-report.shs`
  - `STATUS: PASS gpu web/db offload benchmark report`; regenerated the
    GPU web/DB benchmark manual/report/table and added
    `web_embedding_cuda_measured | cuda | web_embedding_16x512_response_match |
    gpu_web_embedding_batch | device_time_us=208 | native-device-measured`
    plus `web_rank_cuda_measured | cuda | web_rank_32x256_response_match |
    gpu_web_rank_batch | device_time_us=211 | native-device-measured`.
- `sh scripts/check/check-gpu-web-db-offload-benchmark-report.shs`
  - `STATUS: PASS gpu web/db offload benchmark report`; regenerated the
    GPU web/DB benchmark manual/report/table and added
    `web_transform_device_validated_contract | cuda |
    web_transform_8x2048_response_match | gpu_web_transform_batch |
    device_time_us=51 | production-device-validated-contract`, so the
    published report now carries production-facing CPU/GPU response agreement
    and strict device-backend timing for transform routes as well as
    inference, embedding, and rank.
- `sh scripts/check/check-gpu-web-db-offload-native-device-probe.shs`
  - `STATUS: PASS gpu web/db native device probe`; the measured-row guard now
    accepts positive native timing for DB vector/columnar targets and web
    inference/embedding/rank/transform targets, while still rejecting fallback
    and zero-time rows.
- `bin/simple check src/lib/nogc_async_mut/web_framework/app.spl src/lib/nogc_async_mut/web_framework/dispatcher.spl test/01_unit/lib/nogc_async_mut/web_framework/dispatcher_spec.spl src/lib/nogc_sync_mut/web_framework/gpu_offload.spl src/lib/nogc_sync_mut/web_framework/__init__.spl test/01_unit/lib/nogc_sync_mut/web_framework/gpu_offload_spec.spl`
  - passed after keeping `WebApp` route helpers synchronized with the embedded
    dispatcher router and adding sync transform framework validation coverage.
- `SIMPLE_LIB=src bin/simple test test/01_unit/lib/nogc_async_mut/web_framework/dispatcher_spec.spl --mode=interpreter --clean`
  - 9 tests passed, including app-level GPU route adoption configured through
    `WebApp` ergonomic methods and dispatched through the configured
    dispatcher.
- `SIMPLE_LIB=src bin/simple test test/01_unit/lib/nogc_sync_mut/web_framework/gpu_offload_spec.spl --mode=interpreter --clean`
  - 14 tests passed, including framework transform response replacement after
    native candidate agreement and CPU-authoritative mismatch fallback.
- `SIMPLE_LIB=src bin/simple spipe-docgen test/01_unit/lib/nogc_async_mut/web_framework/dispatcher_spec.spl test/01_unit/lib/nogc_sync_mut/web_framework/gpu_offload_spec.spl --output doc/06_spec --no-index`
  - regenerated 2 complete framework GPU manuals; remaining warnings are
    existing short-document warnings.
- `bin/simple check src/lib/nogc_async_mut/web_framework/dispatcher.spl test/01_unit/lib/nogc_async_mut/web_framework/dispatcher_spec.spl`
  - passed after adding a dispatcher validated-adoption advancing path that
    carries strict native queue state across production-facing web replacements.
- `SIMPLE_LIB=src bin/simple test test/01_unit/lib/nogc_async_mut/web_framework/dispatcher_spec.spl --mode=interpreter --clean`
  - 8 tests passed, including two sequential validated native dispatcher
    replacements with submitted/completed/GPU-hit queue counters advancing.
- `SIMPLE_LIB=src bin/simple spipe-docgen test/01_unit/lib/nogc_async_mut/web_framework/dispatcher_spec.spl --output doc/06_spec --no-index`
  - regenerated 1 complete dispatcher GPU adoption manual; remaining warnings
    are existing toolchain warnings and a short-doc warning.
- `bin/simple check src/lib/nogc_async_mut/web_framework/app.spl src/lib/nogc_async_mut/web_framework/dispatcher.spl test/01_unit/lib/nogc_async_mut/web_framework/dispatcher_spec.spl`
  - passed after adding app-level mixed non-inference WebApp route validation
    through the reusable all-GPU web profile, plus configured proxy forwarding
    CPU-ownership coverage through the same product-facing WebApp surface.
- `SIMPLE_LIB=src bin/simple test test/01_unit/lib/nogc_async_mut/web_framework/dispatcher_spec.spl --mode=interpreter --clean --sequential`
  - 11 tests passed, including sequential embedding and transform route
    replacement through `WebApp`, strict native backend timing, CPU/GPU
    response agreement, advancing submitted/completed/GPU-hit queue state, and
    configured proxy forwarding staying CPU-owned under `web_gpu_profile_all`.
- `SIMPLE_LIB=src bin/simple spipe-docgen test/01_unit/lib/nogc_async_mut/web_framework/dispatcher_spec.spl --output doc/06_spec --no-index`
  - regenerated 1 complete dispatcher GPU adoption manual; remaining warnings
    are existing toolchain warnings and a short-doc warning.
- `bin/simple check src/lib/nogc_sync_mut/database/nosql_offload.spl src/lib/nogc_sync_mut/database/__init__.spl test/01_unit/lib/nogc_sync_mut/database/nosql_document_offload_spec.spl`
  - passed after adding a RAM NoSQL document-filter measured-native replacement
    adapter through the strict `GpuWdbDeviceBackend` runner.
- `SIMPLE_LIB=src bin/simple test test/01_unit/lib/nogc_sync_mut/database/nosql_document_offload_spec.spl --mode=interpreter --clean`
  - 13 tests passed, including native document ID match replacement, mismatch
    fallback, and perf-only backend rejection.
- `SIMPLE_LIB=src bin/simple spipe-docgen test/01_unit/lib/nogc_sync_mut/database/nosql_document_offload_spec.spl --output doc/06_spec --no-index`
  - regenerated 1 complete NoSQL document offload manual; remaining warnings
    are existing toolchain warnings and a short-doc warning.
- `bin/simple check src/lib/nogc_async_mut/http_server/proxy.spl test/01_unit/lib/nogc_async_mut/http_server/async_reverse_proxy_spec.spl`
  - passed after fixing fixed-body streaming admission to use declared
    `Content-Length` instead of only the currently buffered body fragment.
- `bin/simple check src/lib/nogc_async_mut/http_server/worker.spl src/lib/nogc_async_mut/http_server/proxy.spl test/01_unit/lib/nogc_async_mut/http_server/async_reverse_proxy_spec.spl`
  - passed after making the worker upload streaming decision explicit from
    chunked transfer state or declared `Content-Length` above the worker
    buffering limit.
- `SIMPLE_LIB=src bin/simple test test/01_unit/lib/nogc_async_mut/http_server/async_reverse_proxy_spec.spl --mode=interpreter`
  - passed after fixing the response-header slice typing path and tightening
    upgrade-tunnel client reads until the upstream 101 response buffer is
    drained; clean run now reports 86 examples passed and 0 failed.
- `bin/simple check src/lib/nogc_async_mut/http_server/proxy.spl src/lib/nogc_async_mut/http_server/parser.spl src/lib/nogc_async_mut/http_server/worker.spl test/01_unit/lib/nogc_async_mut/http_server/async_reverse_proxy_spec.spl`
  - passed after keeping the worker upload streaming decision explicit,
    narrowing raw header parsing to the first `\r\n\r\n` boundary, and replacing
    proxy `Content-Length` `parse_int()` use with a native-stable decimal parser.
- `SIMPLE_LIB=src bin/simple spipe-docgen test/01_unit/lib/nogc_async_mut/http_server/async_reverse_proxy_spec.spl --output doc/06_spec --no-index`
  - regenerated 1 complete async reverse proxy manual; remaining warnings are
    existing toolchain warnings and a short-doc warning.
- `sh scripts/check/check-proxy-live-httpserver-upload.shs`
  - passed after worker-integrated fixed and chunked request-body streaming
    reached the native `HttpServer` proxy fixture. The current passing wrapper
    proves full fixed upload forwarding for `Content-Length: 1048577`, backend
    response forwarding to the client, and raw chunked upload forwarding through
    the worker-level proxy path. Native build still reports known non-critical
    skipped H2/security closure files, but the wrapper completes with
    `STATUS: PASS proxy live HttpServer upload streaming`.
- `bin/simple check src/lib/nogc_async_mut/io/driver.spl src/lib/nogc_async_mut/http_server/worker.spl`
  - passed after adding mode-aware write registration to the async driver and
    removing temporary worker upload trace writes.
- `SIMPLE_LIB=src bin/simple test test/01_unit/lib/nogc_async_mut/http_server/async_reverse_proxy_spec.spl --mode=interpreter`
  - passed after the driver write-readiness patch; 86 examples passed and 0
    failed.
- `bin/simple check src/lib/nogc_async_mut/http_server/proxy.spl src/lib/nogc_async_mut/http_server/worker.spl test/01_unit/lib/nogc_async_mut/http_server/async_reverse_proxy_spec.spl`
  - passed after confirming the worker-integrated request-body streaming path
    remains wired through the proxy policy helpers and worker state machine.
- `SIMPLE_LIB=src bin/simple test test/01_unit/lib/nogc_async_mut/http_server/async_reverse_proxy_spec.spl --mode=interpreter --clean --sequential`
  - 91 examples passed, including fixed-body incremental streaming, raw
    chunked handoff, malformed chunk rejection, staging-byte budgets, and
    backpressure before additional client-body reads.
- `SIMPLE_LIB=src bin/simple spipe-docgen test/01_unit/lib/nogc_async_mut/http_server/async_reverse_proxy_spec.spl --output doc/06_spec --no-index`
  - regenerated 1 complete async reverse-proxy manual; remaining warnings are
    existing toolchain warnings and a short-doc warning.
- `sh scripts/check/check-proxy-live-httpserver-upload.shs`
  - passed with `STATUS: PASS proxy live HttpServer upload streaming`, proving
    the native worker fixture forwards both the large fixed upload and raw
    chunked upload through the live proxy path.

Attempted broader `bin/simple check src/lib`; it exceeded the 120s tool timeout and left no lingering process.

## Remaining

- Live incremental fixed `Content-Length` and chunked client-body proxy uploads
  are now resolved for the native `HttpServer` fixture. Focused checks pass for
  the worker, proxy, driver, and generated live fixture, the async reverse-proxy
  unit spec passes, and `SIMPLE_PROXY_UPLOAD_STRACE=/tmp/simple-proxy-upload-current-413.strace sh scripts/check/check-proxy-live-httpserver-upload.shs`
  completed with `STATUS: PASS proxy live HttpServer upload streaming`. The
  passing run proves full fixed upload forwarding for `Content-Length: 1048577`,
  backend response forwarding back to the client, and raw chunked upload
  forwarding through the worker-level proxy path. The Spark parallel audit
  attempt still hit the GPT-5.3-Codex-Spark quota limit; the normal audit was
  still running after the live gate passed and was closed as superseded.
  Chunked streaming
  preserves raw chunk framing in unit coverage and bounds both pending upstream
  bytes and incomplete chunk staging bytes. Native/cached Simple proxy live throughput
  now has `native_simple_cached_proxy_http_50` evidence beside the
  `python_reference_loopback` rows, with `upstream_reuse=49` and
  `upstream_connects=1` gated by `check-proxy-live-socket-benchmark.shs` and
  `check-proxy-benchmark-report.shs`. The async worker release path also uses
  `async_proxy_pool_can_keep_idle` before returning upstream fds to the pool,
  and the empty-pool guard is covered by the async reverse-proxy unit slice. A
  real native `HttpServer` proxy fixture now passes
  `STATUS: PASS proxy live HttpServer reverse proxy`; remaining proxy work is
  broader native closure cleanup for unrelated skipped H2/security files.
- DB operator integration now has a reusable CPU-authoritative SQL
  join/aggregate adapter for Pure SQL SELECTs and query-facade aggregate
  metadata plus CPU-oracle validation for GPU candidate rows. Shared DB offload
  envelopes now expose explicit validation metadata so callers can distinguish
  validated GPU candidates from normal dispatch-only evidence. Storage-facade
  row/document adapters now also accept GPU candidate ID manifests only after
  CPU-oracle comparison. Pure SQL now has opt-in validated grouped join count
  plus grouped SUM/AVG/MIN/MAX paths that record `gpu-cpu-row-match` for bounded
  engine-owned candidates, and grouped SUM/AVG/MIN/MAX now have measured-native
  replacement evidence. QueryBuilder now exposes live filtered SUM/AVG/MIN/MAX aggregation
  through the join/aggregate offload facade plus measured-native COUNT/SUM/MIN/
  MAX and RAM AVG scalar replacement after CPU-oracle agreement.
  Broader SQL operator semantics remain open for native/hardware GPU execution
  evidence and replacing CPU-owned execution with validated kernel-backed
  operators beyond bounded COUNT/SUM/AVG/MIN/MAX and grouped deterministic shapes.
- Deeper SSD engine adoption beyond DBFS page-cursor row materialization,
  projected scan metadata, projected row-value manifests, validated projected
  materialized-scan candidate row IDs, and QueryBuilder consumption of
  projected SSD rows plus projected COUNT and numeric SUM/AVG/MIN/MAX aggregates after
  validation, including measured-native SSD materialized COUNT/SUM/AVG/MIN/MAX replacement
  at the QueryBuilder aggregate boundary. Storage-mode, query-facade, and
  profile-level SSD materialized scan rows now also have strict measured-native
  replacement gates after CPU-oracle agreement. `SdnTable` can now hand off
  projected SSD materialized rows only when materialized row IDs, table
  CPU-valid row IDs, GPU candidate row IDs, and measured-native production
  device evidence agree. Remaining work is broader true SSD-backed operator
  execution and table-row materialization beyond bounded scan/filter/project
  and scalar aggregate projected-manifest paths.
- Native/hardware GPU backend beyond the deterministic evidence contracts,
  runtime/SFFI device-timing bridge, perf-only CUDA vector/columnar runners, and
  the strict `GpuWdbDeviceBackend` runner boundary plus DB profile-level device
  evidence wiring, web profile device evidence, and direct DB batch device
  execution plus table storage row-batch device execution, the first
  measured-native row replacement gate, the DB query facade measured-native row
  replacement gate, QueryBuilder RAM-only scan/filter/project measured-native
  row replacement, Pure SQL filtered projection measured-native row
  replacement, measured-native vector result replacement, measured-native web
  profile response replacement, framework/dispatcher measured-native web
  response replacement with queue-state advancement, measured-native SQL
  join/aggregate replacement, measured-native RAM NoSQL document-filter
  replacement through lower-level, storage-mode, and profile facades,
  measured-native SSD NoSQL document replacement gate plus Pure SQL grouped
  SUM/AVG/MIN/MAX replacement, QueryBuilder COUNT/SUM/AVG aggregate replacement, QueryBuilder SSD
  materialized COUNT/SUM/AVG aggregate replacement, and storage-mode, query-facade,
  profile-level, and `SdnTable` SSD materialized scan row replacement.
  Remaining work is broader production operator replacement through native
  backend queues that execute real kernels. Current measured rows prove real
  CUDA kernel execution for vector-batch, columnar scan, join/aggregate, NoSQL
  document-filter, and web-inference contract shapes; vector-search and SQL
  join/aggregate replacement now require CPU-oracle agreement at their reusable
  facade boundaries, and web profile response replacement now covers both
  inference and transform route kinds. Measured CUDA evidence now covers
  web-inference, web-embedding, web-rank, and web-transform contract shapes.
  Framework-level adoption now covers sync controller helpers, async
  dispatcher adoption, app-level route/profile configuration through `WebApp`,
  mixed non-inference embedding/transform route replacement through the
  reusable all-GPU profile with advancing queue-state evidence, and configured
  proxy forwarding preserving CPU ownership under that all-GPU profile.
  Remaining non-inference web route work is production throughput beyond
  perf-only measured contract rows and validated response-adoption API coverage.
  The strict runner prevents mock/perf-only paths from claiming production
  device execution.
- Native/hardware GPU performance benchmark reports beyond the compiled WAL
  timing row, proxy live socket report, and host-safe GPU web/DB benchmark
  contract report. The GPU web/DB benchmark report now includes
  `db_vector_cuda_measured`, `db_columnar_scan_cuda_measured`,
  `db_join_aggregate_cuda_measured`, `db_document_filter_cuda_measured`,
  `web_inference_cuda_measured`, `web_embedding_cuda_measured`,
  `web_rank_cuda_measured`, and `web_transform_cuda_measured` from the CUDA
  measured drivers plus `web_inference_device_validated_contract`,
  `web_embedding_device_validated_contract`, and
  `web_rank_device_validated_contract`, and
  `web_transform_device_validated_contract`, which prove production-facing web
  response replacement is gated by CPU/GPU candidate agreement and strict
  device-backend timing for inference, embedding, rank, and transform routes.
  It also includes `web_transform_validated_profile_throughput_contract`, with
  explicit `call_count=4`, `gpu_hits=4`, and aggregate strict-backend device
  timing for repeated transform validation through the web profile boundary.
  The same benchmark contract now includes
  `db_ssd_materialized_scan_device_validated_contract`, which builds a DBFS
  pager/WAL/checkpoint fixture, materializes persisted SSD page cursors, then
  crosses `db_storage_execute_ssd_materialized_scan_with_device_backend_validated`
  with matching CPU/GPU row IDs, `gpu_hits=1`, and strict device timing
  provenance.
  The DB profile path also includes
  `db_ssd_materialized_scan_profile_throughput_contract`, with `call_count=3`,
  `gpu_hits=3`, and aggregate strict-backend timing for repeated DBFS-backed SSD
  materialized scan validation through
  `db_offload_profile_execute_ssd_materialized_scan_device`.
  The row
  `db_ssd_materialized_scan_runtime_queue_throughput_contract` now feeds
  `rt_host_gpu_queue_last_device_time_us()` into the same DB profile SSD
  materialized scan path immediately after host GPU queue completion, with
  `call_count=2`, `gpu_hits=2`, CPU/materialized-row agreement, and
  queue-derived timing provenance.
  The report wrapper
  `scripts/check/check-gpu-web-db-offload-benchmark-report.shs` now passes with
  eleven benchmark examples and writes the measured web inference, embedding,
  rank, and transform rows, all four validated web-response rows, and the
  transform validated throughput-contract plus DBFS-backed SSD materialized
  scan validation, DB profile throughput-contract, and runtime-queue timed DB
  profile throughput-contract rows to the report and metrics table.
  The remaining gap
  is measured production DB/web operator throughput beyond the perf-only CUDA
  DB/web contract rows, validated web-response contract rows, DBFS-backed SSD
  strict-validation, repeated-call throughput contract rows, and queue-level
  runtime-timing contract row, and deterministic web repeated-call throughput
  contract row, not report shape or provenance. The runtime-timing row is still
  last-packet queue timing for a validated fixture, so broad production DB
  throughput remains open.

Current DB/GPU reliability note (2026-06-16):

- `DbOffloadProfile` now exposes
  `db_offload_profile_execute_ssd_documents_device_validated`, a reusable
  production boundary for SSD-backed NoSQL document filters that accepts native
  GPU candidate document IDs instead of implicitly trusting the CPU-filtered
  IDs. The existing convenience helper delegates to this stricter API.
- The DB profile spec now proves that saved SSD NoSQL document filters replace
  CPU authority only when measured native candidate IDs match the CPU oracle;
  mismatched native IDs fall back to CPU with
  `production-gpu-document-mismatch`.
- Evidence refreshed:
  `bin/simple check src/lib/nogc_sync_mut/database/offload_profile.spl test/01_unit/lib/nogc_sync_mut/database/db_offload_profile_spec.spl`,
  `bin/simple test test/01_unit/lib/nogc_sync_mut/database/db_offload_profile_spec.spl --mode=interpreter --clean`,
  and `SIMPLE_LIB=src bin/simple spipe-docgen test/01_unit/lib/nogc_sync_mut/database/db_offload_profile_spec.spl --output doc/06_spec --no-index`.

Current Web/GPU reliability note (2026-06-16):

- `WebGpuRouteOffloadExecution` now carries `gpu_candidate_validated` and
  `validation_reason` directly. Normal route accounting defaults to
  `gpu-candidate-not-evaluated`; strict measured device validation writes
  `production-gpu-web-response-match`,
  `production-gpu-web-response-mismatch`, or
  `production-device-not-measured` into the reusable execution object.
- This mirrors the DB storage execution contract and lets generic web server
  and framework code distinguish GPU queue dispatch evidence from GPU response
  authority without depending only on wrapper-level metadata.
- Evidence refreshed:
  `bin/simple check src/lib/nogc_sync_mut/web_db_offload/web_route.spl src/lib/nogc_sync_mut/web_db_offload/web_profile.spl test/01_unit/lib/nogc_sync_mut/web_db_offload/web_route_profile_spec.spl test/01_unit/lib/nogc_sync_mut/web_framework/gpu_offload_spec.spl`,
  `bin/simple test test/01_unit/lib/nogc_sync_mut/web_db_offload/web_route_profile_spec.spl --mode=interpreter --clean`,
  `bin/simple test test/01_unit/lib/nogc_sync_mut/web_framework/gpu_offload_spec.spl --mode=interpreter --clean`,
  and `SIMPLE_LIB=src bin/simple spipe-docgen test/01_unit/lib/nogc_sync_mut/web_db_offload/web_route_profile_spec.spl test/01_unit/lib/nogc_sync_mut/web_framework/gpu_offload_spec.spl --output doc/06_spec --no-index`.

Current Reverse-Proxy Chunked Upload Hardening Note (2026-06-16):

- Live chunked request-body pass-through now uses the structural chunk parser
  for completion detection instead of substring matching
  `\r\n0\r\n\r\n`. This prevents a legal chunk payload containing
  terminal-looking bytes from prematurely ending the proxied upload.
- The same path now rejects bytes after a structurally complete terminal chunk
  with `chunked-request-body-trailing-bytes`, closing a request-smuggling edge
  at the worker streaming boundary while still forwarding raw chunk framing to
  the backend.
- Upstream response reads now use `async_proxy_upstream_recv_budget(...)` so
  the worker does not schedule a read larger than the remaining configured
  downstream pending-client buffer. The existing post-read
  `async_proxy_pending_client_over_budget(...)` guard remains as a fail-closed
  safety net for header expansion and unexpected backend behavior.
- Evidence refreshed:
  `bin/simple check src/lib/nogc_async_mut/http_server/proxy.spl src/lib/nogc_async_mut/http_server/worker.spl test/01_unit/lib/nogc_async_mut/http_server/async_reverse_proxy_spec.spl`,
  `bin/simple test test/01_unit/lib/nogc_async_mut/http_server/async_reverse_proxy_spec.spl --mode=interpreter --clean`,
  and `SIMPLE_LIB=src bin/simple spipe-docgen test/01_unit/lib/nogc_async_mut/http_server/async_reverse_proxy_spec.spl --output doc/06_spec --no-index`.

Current DB Vector/GPU Reliability Note (2026-06-16):

- Storage-mode DB offload now exposes
  `db_storage_execute_vector_with_device_backend_validated`, converting the
  existing measured-native vector adapter into the common
  `DbStorageOffloadExecution` shape with `gpu_candidate_validated` and
  `validation_reason`.
- `DbOffloadProfile` now exposes
  `db_offload_profile_execute_vector_device`, so DB server code can use the
  same profile/queue/budget boundary for production vector search replacement
  that RAM rows, SSD rows, and NoSQL documents already use.
- CPU vector results remain authoritative unless the native backend has a
  production device claim and GPU candidate result IDs match the CPU oracle;
  mismatches fall back to CPU with `production-gpu-vector-mismatch`.
- Evidence refreshed:
  `bin/simple check src/lib/nogc_sync_mut/database/storage_mode_offload.spl src/lib/nogc_sync_mut/database/offload_profile.spl test/01_unit/lib/nogc_sync_mut/database/db_offload_profile_spec.spl`,
  `bin/simple test test/01_unit/lib/nogc_sync_mut/database/db_offload_profile_spec.spl --mode=interpreter --clean`,
  and `SIMPLE_LIB=src bin/simple spipe-docgen test/01_unit/lib/nogc_sync_mut/database/db_offload_profile_spec.spl --output doc/06_spec --no-index`.

Current DB Query Vector/GPU Reliability Note (2026-06-16):

- The DB query facade now exposes
  `db_query_offload_execute_vector_device_validated`, so DB server callers can
  request measured-native vector-search replacement without dropping below the
  query boundary.
- The function delegates to the storage/profile-compatible vector device gate:
  CPU vector results remain authoritative unless the native backend has a
  production device claim and GPU candidate result IDs match the CPU oracle.
- Evidence refreshed:
  `bin/simple check src/lib/nogc_sync_mut/database/query_offload.spl src/lib/nogc_sync_mut/database/storage_mode_offload.spl test/01_unit/lib/nogc_sync_mut/database/db_query_offload_spec.spl`,
  `bin/simple test test/01_unit/lib/nogc_sync_mut/database/db_query_offload_spec.spl --mode=interpreter --clean`,
  and `SIMPLE_LIB=src bin/simple spipe-docgen test/01_unit/lib/nogc_sync_mut/database/db_query_offload_spec.spl --output doc/06_spec --no-index`.

Current Vector Store Public GPU API Note (2026-06-16):

- `VectorDatabase.search_with_query_device_backend_validated` now wraps the
  DB query vector device validation facade from the vector-store boundary. It
  keeps CPU search as the oracle and returns the shared
  `DbStorageVectorDeviceOffloadExecution` shape for DB server callers.
- The public `std.database` root now exports
  `DbStorageVectorDeviceOffloadExecution`,
  `db_storage_execute_vector_with_device_backend_validated`, and
  `db_query_offload_execute_vector_device_validated`, plus
  `vector_search_profile_allows_gpu`, through the async package root that
  resolves the normal `std.database` import path.
- `doc/07_guide/lib/database/simple_db.md` documents the vector store and DB
  query facade paths, including the rule that GPU dispatch is queue evidence
  while replacement requires `gpu_candidate_validated` and
  `cpu_authoritative == false`; it also documents the root eligibility helper.
- Evidence refreshed:
  `bin/simple check src/lib/nogc_sync_mut/database/vector/store.spl src/lib/nogc_sync_mut/database/vector/__init__.spl src/lib/nogc_sync_mut/database/__init__.spl src/lib/nogc_async_mut/database/__init__.spl test/01_unit/lib/nogc_sync_mut/database/vector/vector_store_search_offload_spec.spl`,
  `SIMPLE_LIB=src bin/simple check /tmp/root_vector_api_check_*.spl` style
  root import smokes for the vector device type/functions and eligibility
  helper,
  `bin/simple test test/01_unit/lib/nogc_sync_mut/database/vector/vector_store_search_offload_spec.spl --mode=interpreter --clean`,
  and `SIMPLE_LIB=src bin/simple spipe-docgen test/01_unit/lib/nogc_sync_mut/database/vector/vector_store_search_offload_spec.spl --output doc/06_spec --no-index`.

Current Async Web Framework GPU Public API Note (2026-06-17):

- The async `std.web_framework` package root now re-exports the controller-facing
  GPU route config, execution, adoption, validated-adoption, scheduling, and
  accumulation helper types/functions used by `AppDispatcher` GPU adoption
  methods.
- This makes production async web-server callers able to type and call the
  validated dispatcher GPU adoption boundary from `std.web_framework` rather
  than importing internal sync helper modules directly.
- Evidence refreshed:
  `SIMPLE_LIB=src bin/simple check` root import smokes for
  `WebFrameworkGpuRouteValidatedAdoption`,
  `web_framework_gpu_route_execute_device_validated_for_action`,
  `WebFrameworkGpuRouteConfig`, `WebFrameworkGpuRouteAdoption`, and
  `web_framework_gpu_route_used_gpu`,
  `bin/simple check src/lib/nogc_async_mut/web_framework/__init__.spl test/01_unit/lib/nogc_async_mut/web_framework/dispatcher_spec.spl`,
  `bin/simple test test/01_unit/lib/nogc_async_mut/web_framework/dispatcher_spec.spl --mode=interpreter --clean`,
  and `SIMPLE_LIB=src bin/simple spipe-docgen test/01_unit/lib/nogc_async_mut/web_framework/dispatcher_spec.spl --output doc/06_spec --no-index`.

Current Reverse Proxy Response Framing Note (2026-06-17):

- `async_proxy_filter_response_headers` now appends `Connection: close` after
  stripping upstream hop-by-hop response headers. This keeps downstream
  response framing explicit after removing upstream `Transfer-Encoding`,
  `Connection`, `Keep-Alive`, `TE`, `Trailer`, and `Upgrade`.
- The existing reverse proxy spec already asserted the close-delimited response
  policy; the implementation now matches that policy on the filtered response
  header path.
- Evidence refreshed:
  `bin/simple check src/lib/nogc_async_mut/http_server/proxy.spl test/01_unit/lib/nogc_async_mut/http_server/async_reverse_proxy_spec.spl`,
  public `std.http_server.async_proxy_filter_response_headers` import coverage
  in `test/01_unit/lib/nogc_async_mut/http_server/async_reverse_proxy_spec.spl`,
  `bin/simple test test/01_unit/lib/nogc_async_mut/http_server/async_reverse_proxy_spec.spl --mode=interpreter --clean`,
  and `SIMPLE_LIB=src bin/simple spipe-docgen test/01_unit/lib/nogc_async_mut/http_server/async_reverse_proxy_spec.spl --output doc/06_spec --no-index`.

Current Async Database GPU Public API Note (2026-06-17):

- The async `std.database` package root now mirrors the strict validated sync DB
  offload facades for RAM rows, SSD materialized rows, RAM/SSD documents, NoSQL
  document filters, and vector search.
- Public async DB/server callers can import the validated execution types and
  helpers from `std.database` without reaching into sync implementation modules.
- The focused export spec now calls
  `db_query_offload_execute_rows_device_validated` through `std.database` and
  proves a matching production GPU candidate flips CPU authority off with
  `production-gpu-row-match`.
- The same export spec now also calls
  `nosql_document_offload_execute_device_validated` through `std.database` and
  proves matching production GPU document IDs flip CPU authority off with
  `production-gpu-document-match`.
- The export spec now also calls
  `db_query_offload_execute_vector_device_validated` through `std.database` and
  proves matching production GPU vector-search results flip CPU authority off
  with `production-gpu-vector-match`.
- The export spec now also calls
  `db_storage_execute_ssd_materialized_scan_with_device_backend_validated`
  through `std.database` and proves matching production GPU row IDs replace
  CPU authority for a clean SSD materialized scan with
  `production-gpu-row-match`.
- The export spec now also calls
  `db_storage_execute_ssd_documents_with_device_backend_validated` through
  `std.database` and proves matching production GPU document IDs replace CPU
  authority for a saved SSD-backed NoSQL document filter with
  `production-gpu-document-match`.
- Evidence refreshed:
  `bin/simple check src/lib/nogc_async_mut/database/__init__.spl test/01_unit/lib/nogc_async_mut/database/database_gpu_offload_exports_spec.spl`,
  `bin/simple test test/01_unit/lib/nogc_async_mut/database/database_gpu_offload_exports_spec.spl --mode=interpreter --clean`,
  and `SIMPLE_LIB=src bin/simple spipe-docgen test/01_unit/lib/nogc_async_mut/database/database_gpu_offload_exports_spec.spl --output doc/06_spec --no-index`.

Current Web NGINX Live Parser Recovery Note (2026-06-17):

- `scripts/check/check-web-server-nginx-live-compare.shs` now exposes
  `--self-test-nginx-live-parser`, a non-mutating host-safe parser/status gate
  for the live Simple-vs-NGINX comparison wrapper.
- The self-test verifies `wrk` RPS parsing, p99 unit conversion for `us`, `ms`,
  and `s`, socket-error accumulation, `measured` row classification, and
  `measured_with_failures` classification without requiring `wrk`, `nginx`, or
  live servers.
- Evidence refreshed:
  `sh -n scripts/check/check-web-server-nginx-live-compare.shs` and
  `sh scripts/check/check-web-server-nginx-live-compare.shs --self-test-nginx-live-parser`.

Current External Web Measured Row Contract Note (2026-06-17):

- `scripts/check/check-web-server-nginx-compare-report.shs` now accepts strict
  measured producer rows through `WEB_SERVER_EXTERNAL_COMPARE_MEASURED_OUTPUT`.
- Producers must emit lines shaped
  `WEB_SERVER_EXTERNAL_COMPARE_MEASURED=workload|simple_target|external_baseline|simple_rps|external_rps|simple_p99_ms|external_p99_ms|throughput_mbps|failures|reason`.
- The parser accepts only known workload/simple-target/baseline tuples,
  positive Simple and external RPS values, non-negative p99/throughput/failure
  values, and classifies rows as `measured` or `measured_with_failures`.
  Unknown rows, wrong targets, malformed numbers, and zero-RPS rows are ignored.
- This gives future Caddy, H2O, HAProxy, Envoy, and dynamic-route producer
  wrappers a stable way to replace `ready_unmeasured` rows without hand-editing
  the metrics table.
- Evidence refreshed:
  `sh -n scripts/check/check-web-server-nginx-compare-report.shs`,
  `sh scripts/check/check-web-server-nginx-compare-report.shs --self-test-external-web-measured-parser`,
  `sh scripts/check/check-web-server-nginx-compare-report.shs --self-test-tool-row-classification`,
  and `sh scripts/check/check-web-server-nginx-compare-report.shs`.

Current NGINX Live Producer Integration Note (2026-06-17):

- `scripts/check/check-web-server-nginx-live-compare.shs` now writes
  `build/perf/web_server_nginx_compare/live-nginx-measured-rows.env` during
  live Simple-vs-NGINX runs.
- The file contains strict `WEB_SERVER_EXTERNAL_COMPARE_MEASURED=...` producer
  rows for `static_1kb` and `static_1mb`, matching the base report consumer
  contract. This connects the live NGINX wrapper to the report's generic
  measured-row input path instead of relying only on preserved table rows.
- The wrapper exposes `--self-test-nginx-live-producer-lines` to validate
  producer-line formatting, throughput selection, failure aggregation, and
  measured/failure reason selection without starting servers.
- Evidence refreshed:
  `sh -n scripts/check/check-web-server-nginx-live-compare.shs`,
  `sh scripts/check/check-web-server-nginx-live-compare.shs --self-test-nginx-live-parser`,
  `sh scripts/check/check-web-server-nginx-live-compare.shs --self-test-nginx-live-producer-lines`,
  `sh scripts/check/check-web-server-nginx-live-compare.shs`, and
  `WEB_SERVER_EXTERNAL_COMPARE_MEASURED_OUTPUT="$(cat build/perf/web_server_nginx_compare/live-nginx-measured-rows.env)" sh scripts/check/check-web-server-nginx-compare-report.shs`.

Current Dynamic Route Producer Integration Note (2026-06-17):

- `scripts/check/check-web-server-dynamic-gpu-route-compare.shs` now writes
  `build/perf/web_server_nginx_compare/dynamic-gpu-route-measured-rows.env`
  when live dynamic GPU and CPU route URLs are configured and measured with
  `wrk`.
- The producer file uses the same strict
  `WEB_SERVER_EXTERNAL_COMPARE_MEASURED=...` contract for
  `dynamic_gpu_plaintext` and `dynamic_gpu_json` rows. On hosts without live
  route URLs, the wrapper still records `live-fixture-unavailable` and creates
  an empty producer file instead of emitting fake measured rows.
- The wrapper exposes `--self-test-dynamic-route-producer-lines` to validate
  dynamic producer-line formatting, reason selection, and failure propagation
  without starting live route servers.
- Evidence refreshed:
  `sh -n scripts/check/check-web-server-dynamic-gpu-route-compare.shs`,
  `sh scripts/check/check-web-server-dynamic-gpu-route-compare.shs --self-test-dynamic-route-parser`,
  `sh scripts/check/check-web-server-dynamic-gpu-route-compare.shs --self-test-dynamic-route-producer-lines`,
  `sh scripts/check/check-web-server-dynamic-gpu-route-compare.shs`, and a
  synthetic `WEB_SERVER_EXTERNAL_COMPARE_MEASURED_OUTPUT` consumer run through
  `scripts/check/check-web-server-nginx-compare-report.shs` proving the base
  report accepts dynamic measured rows.

Current Web Producer Auto-Consume Note (2026-06-17):

- `scripts/check/check-web-server-nginx-compare-report.shs` now automatically
  reads measured producer files from
  `build/perf/web_server_nginx_compare/live-nginx-measured-rows.env` and
  `build/perf/web_server_nginx_compare/dynamic-gpu-route-measured-rows.env`
  before applying any explicit `WEB_SERVER_EXTERNAL_COMPARE_MEASURED_OUTPUT`.
- This makes normal report regeneration preserve real measured rows emitted by
  the live wrappers without requiring a manual environment-variable handoff.
  Explicit environment input still wins when a caller needs to inject or test
  measured rows.
- Evidence refreshed:
  `sh -n scripts/check/check-web-server-nginx-compare-report.shs`,
  `sh scripts/check/check-web-server-nginx-compare-report.shs --self-test-external-web-measured-parser`,
  and `sh scripts/check/check-web-server-nginx-compare-report.shs`.

Current DB Producer Auto-Consume Note (2026-06-17):

- `scripts/check/check-gpu-web-db-offload-benchmark-report.shs` now persists
  external DB baseline producer output to
  `build/perf/gpu_web_db_offload/external-db-baseline-measured-rows.env`.
- The report generator auto-consumes that file together with explicit
  `GPU_WDB_EXTERNAL_DB_BASELINE_OUTPUT`, de-duplicating identical measured
  lines before inserting strict `external-db-measured` rows.
- On this host the producer file is empty because ClickHouse, DuckDB,
  PostgreSQL/pgbench, and MongoDB shells are not installed/configured, so the
  normal report remains on explicit unavailable-tool rows.
- Evidence refreshed:
  `sh -n scripts/check/check-gpu-web-db-offload-benchmark-report.shs`,
  `sh scripts/check/check-gpu-web-db-offload-benchmark-report.shs --self-test-external-db-measured-parser`,
  and `sh scripts/check/check-gpu-web-db-offload-benchmark-report.shs`.

Current Proxy External Dynamic Route URL Note (2026-06-17):

- `scripts/check/check-web-server-proxy-external-live-compare.shs` now sources
  `build/perf/gpu_web_db_offload/external-fixtures.env` by default before
  checking live proxy and dynamic route URL pairs.
- The same producer emits strict measured rows for
  `dynamic_gpu_plaintext|native_simple_gpu_route_plaintext|cpu_simple_plaintext`
  and `dynamic_gpu_json|native_simple_gpu_route_json|cpu_simple_json` when the
  corresponding GPU and CPU route URLs are configured.
- Evidence refreshed:
  `sh -n scripts/check/check-web-server-proxy-external-live-compare.shs`,
  `sh scripts/check/check-web-server-proxy-external-live-compare.shs --self-test-proxy-external-producer-lines`,
  `sh scripts/check/check-web-server-proxy-external-live-compare.shs --self-test-proxy-env-file-source`,
  and
  `sh scripts/check/check-web-server-nginx-compare-report.shs --self-test-external-web-measured-parser`.

Current External DB Standard Shape Producer Note (2026-06-17):

- `scripts/check/check-gpu-web-db-offload-external-db-baselines.shs` now uses
  named standard-shape commands for live DB baselines:
  ClickBench-style scan/filter/project over `numbers(1024)`, TPC-H-style
  join/aggregate/group/order/limit over 1024x16 rows for DuckDB/PostgreSQL, and
  a Mongo/YCSB-style document filter over up to 1024 documents.
- The wrapper exposes `--self-test-standard-shape-manifest` so the workload
  shape can be verified without requiring ClickHouse, DuckDB, PostgreSQL, or
  MongoDB to be installed on the host.
- Evidence refreshed:
  `sh -n scripts/check/check-gpu-web-db-offload-external-db-baselines.shs`,
  `sh scripts/check/check-gpu-web-db-offload-external-db-baselines.shs --self-test-standard-shape-manifest`,
  `sh scripts/check/check-gpu-web-db-offload-external-db-baselines.shs --self-test`,
  and
  `sh scripts/check/check-gpu-web-db-offload-external-db-baselines.shs --self-test-env-file-source`.

Current External DB Manifest Report Note (2026-06-17):

- `scripts/check/check-gpu-web-db-offload-external-db-baselines.shs` now exposes
  `--print-standard-shape-manifest`, printing the exact live DB baseline command
  shapes used by the producer.
- `scripts/check/check-gpu-web-db-offload-benchmark-report.shs` embeds that
  manifest under `External DB Standard Shape Manifest` in
  `doc/09_report/perf/gpu_web_db_offload_benchmark_2026-06-16.md`, so DB
  baseline reports carry the workload command evidence next to the external
  baseline status/measured rows.
- Evidence refreshed:
  `sh scripts/check/check-gpu-web-db-offload-external-db-baselines.shs --print-standard-shape-manifest`,
  `sh scripts/check/check-gpu-web-db-offload-benchmark-report.shs`, and
  `grep -n "External DB Standard Shape Manifest" doc/09_report/perf/gpu_web_db_offload_benchmark_2026-06-16.md`.

Current Dynamic Route Env Handoff Note (2026-06-17):

- `scripts/check/check-web-server-dynamic-gpu-route-compare.shs` now sources
  `build/perf/gpu_web_db_offload/external-fixtures.env` before reading
  `DYNAMIC_GPU_PLAINTEXT_URL`, `DYNAMIC_CPU_PLAINTEXT_URL`,
  `DYNAMIC_GPU_JSON_URL`, and `DYNAMIC_CPU_JSON_URL`.
- This aligns the standalone dynamic route producer with the generated
  readiness env handoff already used by the proxy external and DB baseline
  producers.
- Evidence refreshed:
  `sh -n scripts/check/check-web-server-dynamic-gpu-route-compare.shs`,
  `sh scripts/check/check-web-server-dynamic-gpu-route-compare.shs --self-test-dynamic-route-env-file-source`,
  `sh scripts/check/check-web-server-dynamic-gpu-route-compare.shs --self-test-dynamic-route-producer-lines`,
  and `sh scripts/check/check-web-server-dynamic-gpu-route-compare.shs`.

Current External DB Query Override Handoff Note (2026-06-17):

- `scripts/check/check-gpu-web-db-offload-external-fixture-readiness.shs` now
  writes optional `CLICKHOUSE_SCAN_FILTER_PROJECT_QUERY`,
  `DUCKDB_TPCH_Q3_JOIN_AGGREGATE_QUERY`,
  `POSTGRES_TPCH_Q3_JOIN_AGGREGATE_QUERY`, and
  `MONGO_YCSB_DOCUMENT_FILTER_EVAL` slots into the generated
  `build/perf/gpu_web_db_offload/external-fixtures.env`.
- Empty override slots are safe: the external DB baseline producer reapplies the
  default ClickBench/TPC-H/YCSB command shapes after sourcing the env file.
- Evidence refreshed:
  `sh scripts/check/check-gpu-web-db-offload-external-db-baselines.shs --self-test-empty-query-env-defaults`,
  `sh scripts/check/check-gpu-web-db-offload-external-fixture-readiness.shs --self-test-write-env-template`,
  `sh scripts/check/check-gpu-web-db-offload-external-fixture-readiness.shs --self-test-setup-checklist`,
  and `sh scripts/check/check-gpu-web-db-offload-external-fixture-readiness.shs`.

Current External Suite Runner Note (2026-06-17):

- `scripts/check/check-gpu-web-db-offload-external-suite.shs` is now the
  canonical ordered runner for fixture-ready hosts. It refreshes the fixture
  handoff files, runs readiness, NGINX/static/proxy/dynamic web producers, DB
  baseline producer/report generation, and artifact consistency.
- `--dry-run` prints the exact step order without running producers; 
  `--self-test-plan` verifies the step manifest without requiring external
  services.
- Evidence refreshed:
  `sh -n scripts/check/check-gpu-web-db-offload-external-suite.shs`,
  `sh scripts/check/check-gpu-web-db-offload-external-suite.shs --self-test-plan`,
  and `sh scripts/check/check-gpu-web-db-offload-external-suite.shs --dry-run`.

Current External Suite Plan Artifact Note (2026-06-17):

- `scripts/check/check-gpu-web-db-offload-external-suite.shs --write-plan-artifacts`
  writes `doc/09_report/perf/gpu_web_db_offload_external_suite_2026-06-17.md`
  and `doc/10_metrics/perf/gpu_web_db_offload_external_suite.md`.
- The report records the ordered external-suite steps and the current
  missing-by-category fixture blockers without running live producers. It now
  includes suite-step count, missing-fixture item count, and a
  `READY`/`WAITING_ON_FIXTURES` verdict. The report and metrics table also
  embed readiness bootstrap status, including `bootstrap_container_engine`, so
  the suite handoff records local container bootstrap viability. They also
  include a `Handoff Artifacts` section with direct paths to the generated
  fixture env/checklist/bootstrap/template/env-fields/blocker-manifest/
  runbook/action/missing-category files.
- The suite writes
  `build/perf/gpu_web_db_offload/external-fixture-env-fields.tsv`, a
  side-effect-free machine-readable readiness-item to env-variable map for
  fixture automation. The suite advertises it through the
  `external-suite-handoff=env_fields|...` status row.
- The suite writes
  `build/perf/gpu_web_db_offload/external-fixture-blockers.tsv`, a
  side-effect-free machine-readable blocker manifest that combines missing
  category, readiness item, env variable when applicable, and next action. The
  suite advertises it through the `external-suite-handoff=blocker_manifest|...`
  status row.
- The suite also writes
  `build/perf/gpu_web_db_offload/external-fixture-next-actions.md`, a
  side-effect-free missing-category-to-action handoff for fixture operators.
  The suite passes the same fixture env file used by refresh/preflight into
  that writer, so filled URL values are reflected consistently. The generated
  file records its missing-data source for resumed-session provenance and now
  includes a `Fixture Env Fields` table mapping missing URL-backed readiness
  items to the exact `external-fixtures.env` variables.
- Evidence refreshed:
  `sh scripts/check/check-gpu-web-db-offload-external-suite.shs --self-test-plan-artifacts`,
  `sh scripts/check/check-gpu-web-db-offload-external-suite.shs --write-plan-artifacts`,
  and
  `sh scripts/check/check-gpu-web-db-offload-recovery-harness-self-tests.shs --check-current-artifacts`.

Current External Suite Status Note (2026-06-17):

- `scripts/check/check-gpu-web-db-offload-external-suite.shs --status` prints
  the external-suite step count, missing fixture item count, and readiness
  verdict without opening report files or running live producers.
- Current host output reports `suite_steps|25`,
  `missing_fixture_items|26`, `required_missing_fixture_items|23`,
  `optional_missing_fixture_items|3`, and `verdict|WAITING_ON_FIXTURES`.
  It also emits `external-suite-missing=<category>|<items>` rows for
  `web_proxy_tools`, `db_tools`, `proxy_fixture_urls`, `dynamic_route_urls`,
  `reference_fixture_urls`, and `db_service_urls`, plus
  `external-suite-handoff=<name>|<path>` rows for the
  generated handoff files. `--status-json` emits the same status, missing
  category, step, and handoff data as compact JSON for automation, and
  `--write-status-json` persists that view at
  `build/perf/gpu_web_db_offload/external-suite-status.json`.
  `--policy-json` and `--write-policy-json` expose the required/optional split
  at `build/perf/gpu_web_db_offload/external-suite-readiness-policy.json`.
  The status self-tests also feed an all-empty missing-by-category fixture file
  and prove the `verdict|READY` path.
- Evidence refreshed:
  `sh scripts/check/check-gpu-web-db-offload-external-suite.shs --self-test-status`,
  `sh scripts/check/check-gpu-web-db-offload-external-suite.shs --self-test-status-json`,
  `sh scripts/check/check-gpu-web-db-offload-external-suite.shs --self-test-write-status-json`,
  `sh scripts/check/check-gpu-web-db-offload-external-suite.shs --self-test-policy-json`,
  `sh scripts/check/check-gpu-web-db-offload-external-suite.shs --self-test-write-policy-json`,
  `sh scripts/check/check-gpu-web-db-offload-external-suite.shs --status`, and
  `sh scripts/check/check-gpu-web-db-offload-external-suite.shs --status-json`,
  `sh scripts/check/check-gpu-web-db-offload-recovery-harness-self-tests.shs --check-current-artifacts`.

Current External Fixture Bootstrap Template Note (2026-06-17):

- `scripts/check/check-gpu-web-db-offload-external-fixture-readiness.shs --write-bootstrap-manifest`
  writes `build/perf/gpu_web_db_offload/external-fixture-bootstrap-manifest.tsv`
  with container/tool/url candidates for the missing fixture categories.
- `scripts/check/check-gpu-web-db-offload-external-fixture-readiness.shs --write-docker-compose-template`
  writes `build/perf/gpu_web_db_offload/external-fixture-compose.yaml`.
  Generation is side-effect-free: it does not pull images or start containers.
- `scripts/check/check-gpu-web-db-offload-external-fixture-readiness.shs --write-docker-run-template`
  writes `build/perf/gpu_web_db_offload/external-fixture-docker-run.shs`, an
  executable but not auto-run Docker fallback template for the same local
  Caddy, HAProxy, Envoy, ClickHouse, PostgreSQL, and MongoDB fixtures.
- `scripts/check/check-gpu-web-db-offload-external-fixture-readiness.shs --write-proxy-config-templates`
  writes `build/perf/gpu_web_db_offload/haproxy.cfg` and
  `build/perf/gpu_web_db_offload/envoy.yaml` so the compose template's proxy
  mounts resolve before any container is started.
- `scripts/check/check-gpu-web-db-offload-external-fixture-readiness.shs --write-env-hints`
  writes `build/perf/gpu_web_db_offload/external-fixture-env-hints.md` with
  commented copy/paste URL examples for the generated proxy and DB fixtures; it
  is Markdown rather than a sourceable env file, so generation cannot mark
  readiness rows as ready.
- `scripts/check/check-gpu-web-db-offload-external-fixture-readiness.shs --write-runbook`
  writes `build/perf/gpu_web_db_offload/external-fixture-runbook.md` with the
  reviewed compose/proxy startup command, env-file fill step, refresh/status
  checks, strict `--require-ready` gate, and the guarded suite command.

Current External Suite Refresh Status Note (2026-06-17):

- `scripts/check/check-gpu-web-db-offload-external-suite.shs --refresh-status`
  refreshes `build/perf/gpu_web_db_offload/external-fixture-missing-by-category.env`
  and then prints the same machine-readable status rows as `--status`.
- When `build/perf/gpu_web_db_offload/external-fixtures.env` exists,
  `--refresh-status` and `--preflight` import non-empty readiness URL values
  from that file before computing missing categories. This keeps the generated
  env-file handoff aligned with the suite preflight path.
- Use this after installing external baseline tools or exporting fixture URLs,
  before deciding whether to run the full external suite.
- Evidence refreshed:
  `sh scripts/check/check-gpu-web-db-offload-external-suite.shs --self-test-refresh-status`,
  `sh scripts/check/check-gpu-web-db-offload-external-suite.shs --self-test-refresh-status-env-file`,
  `sh scripts/check/check-gpu-web-db-offload-external-suite.shs --refresh-status`,
  and
  `sh scripts/check/check-gpu-web-db-offload-recovery-harness-self-tests.shs --check-current-artifacts`.

Current External Suite Preflight Note (2026-06-17):

- `scripts/check/check-gpu-web-db-offload-external-suite.shs --preflight`
  refreshes missing-by-category readiness, prints the external-suite status rows,
  and ends with a fixture-ready PASS or fixture-missing WARN.
- Current host output ends with
  `STATUS: WARN gpu web/db external suite preflight missing:26`.
- Evidence refreshed:
  `sh scripts/check/check-gpu-web-db-offload-external-suite.shs --self-test-preflight`,
  `sh scripts/check/check-gpu-web-db-offload-external-suite.shs --preflight`,
  and
  `sh scripts/check/check-gpu-web-db-offload-recovery-harness-self-tests.shs --check-current-artifacts`.

Current External Suite Default Guard Note (2026-06-17):

- The default `scripts/check/check-gpu-web-db-offload-external-suite.shs`
  command now runs preflight first and stops before live producers when
  fixture rows are missing. This prevents a fixture-incomplete host from
  ending a full-suite command with a misleading PASS.
- `--allow-partial` is the explicit escape hatch for local artifact refresh
  while fixtures are still missing; it ends with
  `STATUS: WARN gpu web/db external suite partial`.
- Evidence refreshed:
  `sh scripts/check/check-gpu-web-db-offload-external-suite.shs --self-test-default-guard`,
  `sh scripts/check/check-gpu-web-db-offload-external-suite.shs --self-test-allow-partial`
  and
  `sh scripts/check/check-gpu-web-db-offload-recovery-harness-self-tests.shs`.
