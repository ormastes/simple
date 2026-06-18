# GPU Web/DB Offload Optimization Benchmark Plan

Status: implementation in progress; core harness and producer/consumer
contracts are implemented, external fixture coverage still incomplete.

## Crash-Session Recovery Handoff

The crashed/recovered Codex rollout for this lane was located at
`/home/ormastes/.codex/sessions/2026/06/16/rollout-2026-06-16T04-07-18-019ece9c-bb30-76a1-952f-7233322187d1.jsonl`.
Use this plan and the current worktree as authoritative, because the recovered
harness work has advanced beyond the earlier crash note.

Fast continuation check:

```sh
scripts/check/check-gpu-web-db-offload-recovery-harness-self-tests.shs --check-current-artifacts
```

This check validates the durable Simple-vs-NGINX, DB baseline status,
readiness, recovery self-test, env-template, setup-checklist, and
missing-by-category artifacts without rerunning live benchmark producers.

## Goal

Turn the existing GPU web/DB offload lane from contract-level CUDA evidence
into a production benchmark program that can compare Simple web-server,
reverse-proxy, and DB-server throughput against well-known fast systems without
overclaiming GPU acceleration.

## Current Evidence

Local green evidence already recorded:

- `sh scripts/check/check-proxy-live-httpserver-reliable-suite.shs`
- `sh scripts/check/check-proxy-live-socket-benchmark.shs`
- `sh scripts/check/check-gpu-web-db-offload-native-device-probe.shs`
- `sh scripts/check/check-gpu-web-db-offload-benchmark-report.shs`
- `sh scripts/check/check-gpu-web-db-offload-external-fixture-readiness.shs`
- `sh scripts/check/check-gpu-web-db-offload-external-fixture-readiness.shs --self-test-env-template`
- `sh scripts/check/check-gpu-web-db-offload-external-fixture-readiness.shs --self-test-write-env-template`
- `sh scripts/check/check-gpu-web-db-offload-external-fixture-readiness.shs --self-test-env-template-safe-defaults`
- `sh scripts/check/check-gpu-web-db-offload-external-fixture-readiness.shs --self-test-check-env-file`
- `sh scripts/check/check-gpu-web-db-offload-external-fixture-readiness.shs --self-test-container-engine-status`
- `sh scripts/check/check-gpu-web-db-offload-external-fixture-readiness.shs --self-test-category-summary`
- `sh scripts/check/check-gpu-web-db-offload-external-fixture-readiness.shs --self-test-missing-by-category`
- `sh scripts/check/check-gpu-web-db-offload-external-fixture-readiness.shs --self-test-write-missing-by-category`
- `sh scripts/check/check-gpu-web-db-offload-external-fixture-readiness.shs --self-test-setup-checklist`
- `sh scripts/check/check-gpu-web-db-offload-external-fixture-readiness.shs --self-test-write-setup-checklist`
- `sh scripts/check/check-gpu-web-db-offload-recovery-harness-self-tests.shs`
- `sh scripts/check/check-gpu-web-db-offload-recovery-harness-self-tests.shs --check-current-artifacts`

Current metrics live in:

- `doc/09_report/perf/proxy_live_socket_benchmark_2026-06-16.md`
- `doc/10_metrics/perf/proxy_live_socket_benchmark.md`
- `doc/09_report/perf/gpu_web_db_offload_benchmark_2026-06-16.md`
- `doc/10_metrics/perf/gpu_web_db_offload_benchmark.md`
- `doc/09_report/perf/gpu_web_db_offload_external_fixture_readiness_2026-06-17.md`
- `doc/10_metrics/perf/gpu_web_db_offload_external_fixture_readiness.md`
- `doc/09_report/perf/gpu_web_db_offload_recovery_harness_self_tests_2026-06-17.md`
- `doc/10_metrics/perf/gpu_web_db_offload_recovery_harness_self_tests.md`
- `doc/09_report/perf/web_server_nginx_compare_2026-06-17.md`
- `doc/10_metrics/perf/web_server_nginx_compare.md`

These prove reliability, selected CUDA kernel/device-contract rows, measured
static HTTP rows against NGINX/Caddy/H2O, and measured external DB baseline
rows for ClickHouse, DuckDB, PostgreSQL, MongoDB/YCSB, and Redis/Valkey. They
do not yet prove end-to-end parity for live proxy/dynamic web workloads against
HAProxy, Envoy, Seastar, uWebSockets, or complete TechEmpower-style route
fixtures.

## Current Implementation State

Implemented and verified on the current host:

- NGINX static-file comparison rows are measured through `wrk`; current rows are
  evidence, not speedup claims.
- Caddy/H2O static-file comparison now has an optional live producer at
  `scripts/check/check-web-server-static-external-live-compare.shs`. On hosts
  without Caddy/H2O it exits cleanly with
  `STATUS: WARN tool-unavailable:caddy,h2o`; on hosts with Caddy/H2O or Docker
  for the generated Caddy/H2O fixtures, it emits strict
  `WEB_SERVER_EXTERNAL_COMPARE_MEASURED=...` rows to
  `build/perf/web_server_nginx_compare/static-external-measured-rows.env`.
- HAProxy/Envoy cached reverse-proxy comparison now has a URL-driven producer at
  `scripts/check/check-web-server-proxy-external-live-compare.shs`. On hosts
  without configured proxy fixture URLs it exits cleanly with
  `STATUS: WARN live-fixture-unavailable:proxy-external-urls-not-configured`;
  when `SIMPLE_CACHED_PROXY_URL` plus `HAPROXY_CACHED_PROXY_URL` and/or
  `ENVOY_CACHED_PROXY_URL` are configured, it emits strict cached-proxy
  measured rows to
  `build/perf/web_server_nginx_compare/proxy-external-measured-rows.env`. The
  same wrapper also emits HAProxy upload-streaming rows when
  `SIMPLE_UPLOAD_PROXY_URL` and `HAPROXY_UPLOAD_PROXY_URL` are configured, and
  HAProxy upgrade-tunnel rows when `SIMPLE_TUNNEL_PROXY_URL` and
  `HAPROXY_TUNNEL_PROXY_URL` are configured. It now sources
  `build/perf/gpu_web_db_offload/external-fixtures.env` by default and also
  emits dynamic CPU/GPU route rows when the plaintext or JSON URL pairs are
  configured.
- The base web comparison report now records measured Docker-backed Caddy and
  H2O static rows on this host, and explicit unavailable rows for missing
  HAProxy and Envoy baselines.
- The live NGINX wrapper, dynamic route wrapper, and base web report share the
  strict `WEB_SERVER_EXTERNAL_COMPARE_MEASURED=...` producer/consumer contract.
  Normal web report regeneration auto-consumes producer files under
  `build/perf/web_server_nginx_compare/`.
- Dynamic GPU route rows have parser and producer self-tests plus URL-driven
  live producer coverage through the proxy external wrapper, but remain
  `live-fixture-unavailable` on this host because live CPU/GPU route URLs are
  not configured. The standalone dynamic route wrapper now sources
  `build/perf/gpu_web_db_offload/external-fixtures.env`, matching the generated
  readiness handoff used by the proxy and DB producers.
- DB external baseline rows cover ClickHouse, DuckDB, PostgreSQL,
  MongoDB/YCSB, and Redis/Valkey availability, measured-row parsing, producer
  self-tests, persistence, and auto-consumption under
  `build/perf/gpu_web_db_offload/`.
  The external DB producer now centralizes the ClickBench-style scan/filter,
  TPC-H-style join/aggregate, and YCSB-style document-filter command shapes and
  verifies that manifest with a host-safe self-test before any live DB service
  is required.
- The GPU Web/DB benchmark report now embeds the external DB producer's
  standard-shape manifest under `External DB Standard Shape Manifest`, so each
  report carries the exact ClickBench/TPC-H/YCSB/Redis/ANN-style command shapes
  alongside the external baseline status or measured rows.
- The generated external fixture env template now includes optional
  standard-shape query override variables for ClickHouse, DuckDB, PostgreSQL,
  Mongo/YCSB, Redis/Valkey, and ANN/vector. Empty override variables are safe:
  the DB producer reapplies the default ClickBench/TPC-H/YCSB/Redis/ANN shapes
  after sourcing the env file.
- The external producer sequence is now canonicalized by
  `scripts/check/check-gpu-web-db-offload-external-suite.shs`. Use `--dry-run`
  to print the exact ordered steps. The default suite command runs preflight
  first and stops with a WARN status if fixture rows are still missing; on a
  fixture-ready host it continues to refresh readiness, web/proxy/dynamic-route
  producers, DB baseline producers, reports, and artifact consistency checks.
  Use `--allow-partial` only for explicit local artifact refresh while fixtures
  are still missing; partial mode ends with WARN instead of a full-suite PASS.
- The same suite wrapper can write durable plan artifacts with
  `--write-plan-artifacts`: `doc/09_report/perf/gpu_web_db_offload_external_suite_2026-06-17.md`
  and `doc/10_metrics/perf/gpu_web_db_offload_external_suite.md` record the
  ordered suite steps plus current missing fixture categories. The report also
  includes suite-step count, missing-fixture item count, and a
  `READY`/`WAITING_ON_FIXTURES` verdict. The suite report and metrics table
  also embed the readiness bootstrap status, including
  `bootstrap_container_engine`, so a resumed handoff carries both missing
  fixture categories and local container bootstrap viability. The same report
  and metrics table now include a `Handoff Artifacts` section with direct paths
  to the env file, setup checklist, bootstrap manifest, Compose/docker-run
  templates, env-fields TSV, blocker manifest TSV, env hints, runbook,
  next-actions file, and missing-category files.
- The readiness handoff can now write a sourceable local candidate env file at
  `build/perf/gpu_web_db_offload/external-fixture-local-env-candidates.env`
  with the default localhost URLs for generated HAProxy, Envoy, ClickHouse,
  PostgreSQL, MongoDB, and Redis fixtures. Use
  `--write-local-env-candidates` only after the matching local containers and
  Simple route fixtures are actually running; copy only verified values into
  `external-fixtures.env`. The external suite includes this as the
  `write-local-env-candidates` step and advertises the path through
  `external-suite-handoff=local_env_candidates|...`.
- Optional Seastar/uWebSockets-style plaintext reference baselines are now
  first-class URL-driven handoff rows. Fill `SIMPLE_REFERENCE_PLAINTEXT_URL`
  plus `UWEBSOCKETS_PLAINTEXT_URL` and/or `SEASTAR_PLAINTEXT_URL` to let the
  proxy external producer emit strict `reference_plaintext` measured rows that
  the web comparison report accepts.
- The readiness handoff now writes
  `build/perf/gpu_web_db_offload/external-fixture-env-fields.tsv`, a
  side-effect-free machine-readable map from URL-backed readiness items to the
  exact `external-fixtures.env` variables. The external suite includes this as
  the `write-env-fields` step and advertises the path through
  `external-suite-handoff=env_fields|...`.
- The readiness handoff now writes
  `build/perf/gpu_web_db_offload/external-fixture-blockers.tsv`, a
  side-effect-free machine-readable blocker manifest that combines missing
  category, readiness item, env variable when applicable, and next action. The
  external suite includes this as the `write-blocker-manifest` step and
  advertises the path through `external-suite-handoff=blocker_manifest|...`.
- The readiness handoff now writes
  `build/perf/gpu_web_db_offload/external-fixture-next-actions.md`, a
  side-effect-free missing-category-to-action map generated from the current
  readiness rows. The external suite includes this as the `write-next-actions`
  step and passes the same fixture env file used by refresh/preflight, so
  fixture operators can see the next setup action without reverse mapping raw
  missing-category output. The generated file records its missing-data source,
  for example `fixture-env-file:build/perf/gpu_web_db_offload/external-fixtures.env`.
  It also includes a `Fixture Env Fields` table that maps URL-backed readiness
  items such as `dynamic_gpu_plaintext_url` and `postgres_url` to the exact
  `external-fixtures.env` variables operators must fill.
- `scripts/check/check-gpu-web-db-offload-external-suite.shs --status` prints
  the same suite-step count, missing-fixture count, and verdict directly for
  fast resumed-session checks without opening the report. It also prints
  `external-suite-missing=<category>|<items>` rows so automation can identify
  exactly which fixture category still blocks a full measured run, plus
  `external-suite-handoff=<name>|<path>` rows for the generated fixture
  handoff files. The status self-test covers both blocked and fixture-ready
  verdict paths plus handoff row output. The sibling `--status-json` command
  emits the same suite-step count, verdict, missing categories, and handoff
  paths as a compact JSON object for automation. `--write-status-json`
  persists that JSON view at
  `build/perf/gpu_web_db_offload/external-suite-status.json`.
  `--write-policy-json` persists
  `build/perf/gpu_web_db_offload/external-suite-readiness-policy.json`, which
  separates required fixture blockers from optional reference-baseline gaps.
  On this host after starting the generated Redis, Caddy, H2O, HAProxy, Envoy,
  ClickHouse, PostgreSQL, and MongoDB Docker fixtures and configuring the
  DuckDB CLI image, the split is 11 required missing fixtures and 3 optional
  reference fixture URLs.
- The suite now also writes required-only handoff artifacts for resumed
  sessions that need to separate release-blocking fixture work from optional
  reference baselines:
  `--write-required-env-missing`,
  `--write-required-env-hints`,
  `--write-required-blockers`,
  `--write-completion-audit`, and
  `--write-required-next-actions`. The required gate is
  `scripts/check/check-gpu-web-db-offload-external-suite.shs --require-required-ready`;
  strict suite completion still uses `--require-ready` so optional reference
  baselines are not silently dropped.
- Use `scripts/check/check-gpu-web-db-offload-external-suite.shs --refresh-status`
  after installing tools or exporting fixture URLs; it refreshes
  `build/perf/gpu_web_db_offload/external-fixture-missing-by-category.env`
  before printing the status rows. When
  `build/perf/gpu_web_db_offload/external-fixtures.env` exists, the suite
  imports non-empty readiness URL values from that file before writing the
  missing-by-category handoff, so filling the generated env file is sufficient
  for refresh/preflight status. The env-file reader accepts bare `NAME=value`,
  `export NAME=value`, and simple quoted URL values for known readiness URL
  variables.
- Use `scripts/check/check-gpu-web-db-offload-external-suite.shs --preflight`
  before a full external-suite run. It refreshes readiness, prints the same
  status/category rows, and emits `STATUS: PASS ... preflight ready` or
  `STATUS: WARN ... preflight missing:N`.
- ClickHouse, DuckDB, PostgreSQL, MongoDB/YCSB, and Redis/Valkey now have
  Docker-backed measured external DB rows on this host. The producer uses
  `CLICKHOUSE_CONTAINER`, `DUCKDB_IMAGE`, `POSTGRES_CONTAINER`,
  `MONGO_CONTAINER`, `REDIS_BENCHMARK_CONTAINER`, and the matching service URLs
  in `build/perf/gpu_web_db_offload/external-fixtures.env`.

Remaining blockers before this plan can be marked done:

- Start or configure the matching live Simple proxy URLs for cached proxy,
  upload streaming, and upgrade tunnel rows. The HAProxy and Envoy tool
  containers are ready, but measured proxy rows still require
  `SIMPLE_CACHED_PROXY_URL`, `HAPROXY_CACHED_PROXY_URL`,
  `ENVOY_CACHED_PROXY_URL`, `SIMPLE_UPLOAD_PROXY_URL`,
  `HAPROXY_UPLOAD_PROXY_URL`, `SIMPLE_TUNNEL_PROXY_URL`, and
  `HAPROXY_TUNNEL_PROXY_URL`.
- Start live CPU and GPU dynamic route servers and set
  `DYNAMIC_GPU_PLAINTEXT_URL`, `DYNAMIC_CPU_PLAINTEXT_URL`,
  `DYNAMIC_GPU_JSON_URL`, and `DYNAMIC_CPU_JSON_URL`.
- Start optional Simple/uWebSockets/Seastar plaintext reference fixtures with
  workload parity and set `SIMPLE_REFERENCE_PLAINTEXT_URL`,
  `UWEBSOCKETS_PLAINTEXT_URL`, and `SEASTAR_PLAINTEXT_URL` when available.
The current blocker list is machine-checkable with
`scripts/check/check-gpu-web-db-offload-external-fixture-readiness.shs`. On the
current host it reports `wrk`, `nginx`, Docker-backed Caddy, Docker-backed H2O,
Docker-backed HAProxy, Docker-backed Envoy, Docker-backed ClickHouse,
Docker-backed DuckDB image, Docker-backed PostgreSQL/pgbench, Docker-backed
MongoDB shell, and Docker-backed Redis/Valkey ready, then `STATUS: WARN` with
missing live cached-proxy, upload-proxy, tunnel-proxy, dynamic-route, and
optional Seastar/uWebSockets reference URL requirements. The
same run writes durable readiness artifacts under `doc/09_report/perf/` and
`doc/10_metrics/perf/`; `--self-test-artifacts` verifies that artifact writing
path using temporary output files. `--print-env-template` prints the exact
environment variable contract for live cached-proxy URLs, upload/tunnel proxy
URLs, dynamic-route URLs, optional reference fixture URLs, and DB service URLs;
`--write-env-template` writes it to
`build/perf/gpu_web_db_offload/external-fixtures.env`, and the generated
readiness report embeds the same template for crash-session handoff. The env
file uses empty assignments with commented examples so an unchanged sourced
template cannot turn missing URL rows into ready rows. `--check-env-file`
sources a filled env file and re-runs readiness before live producers are used.
The report also summarizes readiness by category: core load tools, web/proxy
tools, DB tools, proxy fixture URLs, dynamic-route URLs, reference fixture
URLs, and DB service URLs.
The `proxy_fixture_urls` category now covers cached reverse-proxy URLs plus the
HAProxy upload-streaming and upgrade-tunnel fixture URLs:
`SIMPLE_CACHED_PROXY_URL`, `HAPROXY_CACHED_PROXY_URL`,
`ENVOY_CACHED_PROXY_URL`, `SIMPLE_UPLOAD_PROXY_URL`,
`HAPROXY_UPLOAD_PROXY_URL`, `SIMPLE_TUNNEL_PROXY_URL`, and
`HAPROXY_TUNNEL_PROXY_URL`.
The `reference_fixture_urls` category covers the optional plaintext reference
baselines: `SIMPLE_REFERENCE_PLAINTEXT_URL`, `UWEBSOCKETS_PLAINTEXT_URL`, and
`SEASTAR_PLAINTEXT_URL`.
`--missing-by-category`
prints those same blockers as stable `category=item,item` lines for scripts;
`--write-missing-by-category` persists them to
`build/perf/gpu_web_db_offload/external-fixture-missing-by-category.env`.
`--missing-by-category-from-env-file` and
`--write-missing-by-category-from-env-file` provide the same category output
after importing non-empty URL values from a fixture env file.
`--write-setup-checklist` writes the matching tool/service checklist to
`build/perf/gpu_web_db_offload/external-fixture-setup-checklist.md`. The
checklist now includes the external suite `--refresh-status` and `--preflight`
commands before the guarded full external suite run, plus an explicit
`--allow-partial` command for local artifact refresh when fixtures are still
missing. `--write-env-hints` writes
`build/perf/gpu_web_db_offload/external-fixture-env-hints.md`, a non-sourceable
Markdown handoff with localhost URL examples derived from the generated
HAProxy, Envoy, ClickHouse, PostgreSQL, and MongoDB fixture templates.
`--write-runbook` writes
`build/perf/gpu_web_db_offload/external-fixture-runbook.md`, which gives the
side-effect-free fixture preparation sequence and the explicit guarded suite
commands. `--write-docker-run-template` writes
`build/perf/gpu_web_db_offload/external-fixture-docker-run.shs`, an executable
operator template for hosts with Docker but without Docker Compose. The
generated Compose and docker-run proxy fixtures now map
`host.docker.internal` to Docker's `host-gateway`, so Linux Docker hosts can
reach the repo-local Simple proxy upstream at port 8090 without replacing the
upstream address in most local setups. The docker-run fallback is restart-safe
for the generated fixture names: re-running it removes and recreates only its
own `gpu-web-db-*` containers, leaving unrelated containers alone. Bootstrap
status detects both Docker Compose v2 (`docker compose`) and the legacy
`docker-compose` binary before suggesting the docker-run fallback. Bootstrap
status also prints `bootstrap_container_engine` so operators can distinguish a
present Docker/Podman/Nerdctl CLI from a usable container engine before trying
local fixture startup; `bootstrap_local_fixture_bootstrap=possible` is now
reserved for a ready engine, while `engine-unavailable` means the CLI exists
but the daemon/backend must be fixed first. The container-engine classifier has
a host-safe self-test for ready, unavailable, missing, and unknown runtime
states. The durable readiness report and metrics table include a separate
`Bootstrap Status` section so resumed sessions can inspect container-runtime
state without rerunning bootstrap status manually. The normal suite command will
not start benchmark producers until preflight reports ready, and partial mode is
reported as WARN.

For crash-session recovery and quick validation, run
`scripts/check/check-gpu-web-db-offload-recovery-harness-self-tests.shs`. It
checks shell syntax for the recovery harness scripts and aggregates the
non-mutating parser, producer, and readiness self-tests without rerunning native
builds, live servers, or heavyweight benchmark specs. The command writes
durable PASS artifacts under `doc/09_report/perf/` and `doc/10_metrics/perf/`
with one row per syntax/self-test gate; the current recovery artifacts record
74 passed host-safe gates. `--self-test-artifacts` verifies that same
artifact-writing path with temporary report and metrics files. The harness also
validates the fixture environment template, safe-default behavior, setup
checklist, env-file validation, category summary, missing-by-category output,
missing-by-category file writing, env-file import behavior, proxy config
templates, Docker run fallback, machine-readable env-fields TSV, blocker
manifest TSV, env hints, local env candidates, runbook, next-actions handoff,
next-actions env-field mapping, next-actions env-file import behavior, suite
status/preflight guards, status JSON, readiness policy JSON, and suite artifact
writing so setup drift is caught before rerunning live producers.
`--check-current-artifacts` is the fastest crash-session continuation check: it
verifies the current durable web, DB, readiness, and recovery artifacts still
contain the expected measured/status rows and passed-gate evidence. It also
checks the generated fixture env file, setup checklist, bootstrap manifest,
Compose template, executable Docker run fallback, HAProxy/Envoy configs, env
hints, env-fields TSV, blocker manifest TSV, runbook, next-actions handoff,
missing-by-category files, and external-suite status under
`build/perf/gpu_web_db_offload/`.

Local benchmark fixture availability on 2026-06-18:

| Tool | Status |
|---|---|
| `nginx` | available at `/usr/sbin/nginx` |
| `wrk` | available at `/usr/bin/wrk` |
| `haproxy` | Docker-backed fixture ready: `gpu-web-db-haproxy-cached-proxy` |
| `envoy` | Docker-backed fixture ready: `gpu-web-db-envoy-cached-proxy` |
| `caddy` | Docker-backed fixture ready: `gpu-web-db-caddy-static` |
| `h2o` | Docker-backed fixture ready: `gpu-web-db-h2o-static` |

The first local external-comparison gate produces Simple-vs-NGINX static rows
with `wrk` readiness and explicit unavailable-baseline/load-tool statuses. The
live follow-up wrapper now fills measured RPS and p99 latency values for the
local NGINX baseline:

| Workload | Simple RPS | NGINX RPS | RPS ratio | Simple p99 | NGINX p99 | Failures |
|---|---:|---:|---:|---:|---:|---:|
| `static_1kb` | 2120.72 | 13742.27 | 0.154 | 0.628 ms | 0.093 ms | 0 |
| `static_1mb` | 736.16 | 762.85 | 0.965 | 1.770 ms | 1.850 ms | 0 |

These measurements are evidence, not a speedup claim: Simple is below NGINX for
1 KiB and near parity for 1 MiB on this host. Docker-backed Caddy and H2O rows
are now also measured through the static external wrapper:

| Workload | Baseline | Simple RPS | External RPS | RPS ratio | Simple p99 | External p99 | Failures |
|---|---|---:|---:|---:|---:|---:|---:|
| `static_1kb` | Caddy | 2351.70 | 3776.07 | 0.623 | 0.499 ms | 0.409 ms | 0 |
| `static_1mb` | Caddy | 267.30 | 1359.38 | 0.197 | 4.800 ms | 0.930 ms | 0 |
| `static_1kb` | H2O | 2281.64 | 9389.05 | 0.243 | 0.523 ms | 0.123 ms | 0 |
| `static_1mb` | H2O | 261.93 | 1201.20 | 0.218 | 4.780 ms | 1.160 ms | 0 |

Missing server baselines still have explicit unavailable rows in the same
report: HAProxy/Envoy cached reverse-proxy baselines, and HAProxy
upload/upgrade baselines. When those tools are installed, their rows should move from
`external-baseline-unavailable` to `ready_unmeasured` or measured rows rather
than being added as a separate ad hoc table. The base report script now exposes
`--self-test-tool-row-classification` to verify those status transitions without
rewriting report artifacts. The live NGINX wrapper now also exposes
`--self-test-nginx-live-parser` to verify `wrk` parsing, p99 unit conversion,
socket-error accumulation, and measured/failure row classification without
requiring `wrk`, `nginx`, or live servers. The base report script also accepts
strict measured producer rows through `WEB_SERVER_EXTERNAL_COMPARE_MEASURED_OUTPUT`
using lines shaped
`WEB_SERVER_EXTERNAL_COMPARE_MEASURED=workload|simple_target|external_baseline|simple_rps|external_rps|simple_p99_ms|external_p99_ms|throughput_mbps|failures|reason`.
Only known workload/simple-target/baseline tuples with positive RPS values are
accepted. `--self-test-external-web-measured-parser` verifies that contract and
rejects malformed, wrong-target, unknown, and zero-RPS rows.
`scripts/check/check-web-server-nginx-live-compare.shs` is now the first live
producer for that contract: a measured run writes
`build/perf/web_server_nginx_compare/live-nginx-measured-rows.env`, and
`--self-test-nginx-live-producer-lines` verifies the producer format without
starting live servers. Feeding that file back through
`WEB_SERVER_EXTERNAL_COMPARE_MEASURED_OUTPUT` exercises the end-to-end
producer/consumer path. The Caddy/H2O static wrapper writes the sibling
`build/perf/web_server_nginx_compare/static-external-measured-rows.env` file
when either external server is installed, and its
`--self-test-static-external-producer-lines` mode validates both Caddy and H2O
line shapes without live servers. The HAProxy/Envoy cached proxy wrapper writes
`build/perf/web_server_nginx_compare/proxy-external-measured-rows.env` when
configured fixture URLs are provided, and its
`--self-test-proxy-external-producer-lines` mode validates HAProxy cached,
Envoy cached, HAProxy upload, and HAProxy tunnel line shapes without live
servers. The dynamic route wrapper now uses the same contract:
when `DYNAMIC_GPU_PLAINTEXT_URL`, `DYNAMIC_CPU_PLAINTEXT_URL`,
`DYNAMIC_GPU_JSON_URL`, and `DYNAMIC_CPU_JSON_URL` are configured, it writes
`build/perf/web_server_nginx_compare/dynamic-gpu-route-measured-rows.env`.
Without those live fixtures, it leaves the dynamic rows as
`live-fixture-unavailable` and writes no measured producer lines.
`--self-test-dynamic-route-producer-lines` verifies the dynamic row format
without live servers. The base web comparison report now auto-consumes both
producer files before applying explicit `WEB_SERVER_EXTERNAL_COMPARE_MEASURED_OUTPUT`,
so normal report regeneration preserves wrapper-produced measured rows without
manual shell handoff.

The HTTP matrix also includes dynamic GPU route readiness rows:

| Workload | Simple target | Baseline | Status |
|---|---|---|---|
| `dynamic_gpu_plaintext` | `native_simple_gpu_route_plaintext` | `cpu_simple_plaintext` | ready unmeasured |
| `dynamic_gpu_json` | `native_simple_gpu_route_json` | `cpu_simple_json` | ready unmeasured |

These rows map the TechEmpower-style plaintext/JSON route shapes into the
external comparison table. They still need configured live CPU and GPU route
server URLs before any dynamic-route throughput claim.

The live dynamic-route wrapper now exists at
`scripts/check/check-web-server-dynamic-gpu-route-compare.shs`. On this host it
records both dynamic rows as `live-fixture-unavailable` because the CPU and GPU
route server URLs are not configured. When live route servers are available, set
`DYNAMIC_GPU_PLAINTEXT_URL`, `DYNAMIC_CPU_PLAINTEXT_URL`,
`DYNAMIC_GPU_JSON_URL`, and `DYNAMIC_CPU_JSON_URL` so the wrapper can run `wrk`
and replace those rows with measured values. The wrapper also exposes
`--self-test-dynamic-route-parser` to verify `wrk` parsing, p99 unit conversion,
ratio formatting, throughput calculation, and failure classification without
requiring live route servers, plus `--self-test-dynamic-route-producer-lines`
to verify measured producer rows for the base report contract.

The external HTTP reports now include normalized benchmark input evidence in
both `doc/09_report/perf/web_server_nginx_compare_2026-06-17.md` and
`doc/10_metrics/perf/web_server_nginx_compare.md`:

| Field | Current normalized value |
|---|---|
| Payload | Same bytes per compared workload |
| Keep-alive | `wrk` default keep-alive |
| Connections | 1 |
| Threads | 1 |
| Duration | 1 second |
| Worker policy | One measured server worker unless wrapper overrides both sides |
| Logging | Access logging disabled for measured hot path |
| CPU affinity | Not pinned on this host; report must say so |

The generated reports now include reproducibility context:

| Report | Environment evidence |
|---|---|
| `doc/09_report/perf/web_server_nginx_compare_2026-06-17.md` | CPU model, cores, kernel, RAM, storage, CUDA/nvidia-smi visibility, Simple runtime |
| `doc/09_report/perf/gpu_web_db_offload_benchmark_2026-06-16.md` | CPU model, cores, kernel, RAM, storage, CUDA/nvidia-smi visibility, `CUDA_VISIBLE_DEVICES`, Simple runtime |

The GPU Web/DB benchmark report also now contains standard-shape DB rows for
the next DB lane:

| Workload family | Row | Dispatch target | Status |
|---|---|---|---|
| DB batch admission | `db_batch_admission_policy_contract` | `gpu_db_columnar_scan_batch` | host-safe admission policy |
| ClickBench-inspired OLAP scan | `db_clickbench_olap_scan_shape_contract` | `gpu_db_columnar_scan_batch` | standard baseline unavailable |
| TPC-H-style join/aggregate | `db_tpch_join_aggregate_shape_contract` | `gpu_db_join_aggregate_batch` | standard baseline unavailable |
| BenchBase/YCSB document filter | `db_benchbase_ycsb_document_shape_contract` | `gpu_db_document_filter_batch` | standard baseline unavailable |
| ANN vector search | `db_ann_vector_search_shape_contract` | `gpu_db_vector_search_batch` | standard baseline unavailable |
| ClickHouse ClickBench baseline | `db_clickbench_clickhouse_external_baseline_status` | `clickhouse_scan_filter_project` | measured on this host |
| DuckDB TPC-H baseline | `db_tpch_duckdb_external_baseline_status` | `duckdb_tpch_q3_join_aggregate` | measured on this host |
| PostgreSQL TPC-H baseline | `db_tpch_postgresql_external_baseline_status` | `postgresql_tpch_q3_join_aggregate` | measured on this host |
| MongoDB/YCSB baseline | `db_ycsb_mongo_external_baseline_status` | `mongo_ycsb_document_filter` | measured on this host |
| ANN/vector baseline | `db_ann_vector_external_baseline_status` | `ann_vector_topk_recall` | unavailable until fixture/tool is configured |

The admission row proves the DB queue decision surface before dispatch: a coarse
scan batch is admitted to GPU, a join/aggregate batch falls back when the queue
is full, and a tiny document-filter batch remains on CPU. The standard-shape
rows preserve the workload matrix and the Simple dispatch target mapping. They
do not measure an ANN fixture on this host yet. The external DB baseline status
rows make the implemented missing-tool state machine-checkable in the report
instead of leaving it only in prose. ClickHouse, DuckDB, PostgreSQL,
MongoDB/YCSB, and Redis/Valkey now use the strict measured-row producer/parser
contract. Their status rows move to
`external-db-baseline-ready-measured:*` only when a measured wrapper fills real
latency values; CLI/container readiness alone is not treated as throughput
evidence. The report gate now has a measured-row input contract:
external DB wrappers may provide
`GPU_WDB_EXTERNAL_DB_MEASURED=name|dataset|target|time_us` lines through
`GPU_WDB_EXTERNAL_DB_BASELINE_OUTPUT`, and only known DB baseline names with
matching datasets, matching targets, and positive timings are accepted.
`scripts/check/check-gpu-web-db-offload-external-db-baselines.shs` is the local
producer for those lines; it measures only real external commands that are
available locally or configured by connection URL and emits nothing otherwise.
Its `--self-test` mode validates the timing helper and the six strict measured
line shapes, including Redis/Valkey key/value and ANN/vector top-k, without
requiring any external DB installation.
The producer now sources
`build/perf/gpu_web_db_offload/external-fixtures.env` by default before probing
URL-backed DB baselines, so values written by
`check-gpu-web-db-offload-external-fixture-readiness.shs --write-env-template`
can be filled once and reused by the measured DB producer. Override with
`DB_FIXTURE_ENV_FILE=/path/to/env` when using a separate fixture file.
Normal producer runs now print an explicit status line: `STATUS: PASS external
DB baseline producer rows:N` when at least one measured row is emitted, or
`STATUS: WARN tool-unavailable:external-db-baselines` when no configured DB
baseline is available. The benchmark report parser ignores non-measured status
lines and only consumes strict `GPU_WDB_EXTERNAL_DB_MEASURED=...` records.
The report script also has a non-mutating
`--self-test-external-db-measured-parser` mode that proves one valid measured
row is accepted and malformed/wrong-target/zero-time rows are rejected. The
report now persists producer output to
`build/perf/gpu_web_db_offload/external-db-baseline-measured-rows.env` and
auto-consumes that file on normal regeneration, de-duplicating identical
measured lines before inserting strict `external-db-measured` rows.

## External Benchmark References

Use these as benchmark-methodology references, not as direct apples-to-apples
claims unless the same workload and hardware are reproduced locally:

- TechEmpower Framework Benchmarks: plaintext, JSON, DB read/write, ORM,
  collections, fortunes, and update-style web workloads.
  <https://www.techempower.com/benchmarks/>
- TechEmpower source suite: reproducible framework benchmark definitions.
  <https://github.com/techempower/frameworkbenchmarks>
- `wrk`: multithreaded HTTP load generation with epoll/kqueue and Lua scripting.
  <https://github.com/wg/wrk>
- NGINX architecture/perf references: event-driven workers, high concurrency,
  and published HTTP/HTTPS RPS/CPS/throughput methodology.
  <https://blog.nginx.org/blog/inside-nginx-how-we-designed-for-performance-scale>
  <https://blog.nginx.org/blog/testing-the-performance-of-nginx-and-nginx-plus-web-servers>
- HAProxy/NGINX/Envoy/Traefik comparison reference for load-balancer benchmark
  shape and caveats.
  <https://www.loggly.com/blog/benchmarking-5-popular-load-balancers-nginx-haproxy-envoy-traefik-and-alb/>
- Seastar reference for high-performance asynchronous C++ server design.
  <https://seastar.io/>
- ClickBench: reproducible OLAP benchmark and public result dashboard.
  <https://benchmark.clickhouse.com/>
  <https://github.com/ClickHouse/ClickBench>
- TPC-H: standard analytical DB benchmark.
  <https://www.tpc.org/tpch/>
- BenchBase: multi-DBMS SQL benchmark harness for TPC-C, YCSB, and related
  workloads.
  <https://github.com/cmu-db/benchbase>

## Benchmark Matrix

### Web Server / Reverse Proxy

| Workload | Simple Target | External Baselines | Metrics |
|---|---|---|---|
| Static 1 KiB/1 MiB HTTP | native Simple static server | NGINX, Caddy or H2O where installed | RPS, p50/p95/p99, throughput, CPU, RSS |
| Cached reverse proxy | native Simple cached proxy | NGINX proxy, HAProxy, Envoy | RPS, p50/p95/p99, upstream reuse, connects, errors |
| Upload streaming | native Simple proxy upload | NGINX proxy, HAProxy | MiB/s, backpressure, max pending bytes, errors |
| Upgrade tunnel | native Simple tunnel proxy | NGINX proxy, HAProxy | p50/p95/p99 echo latency, binary safety, errors |
| Dynamic GPU route | Simple web route offload | TechEmpower-style plaintext/JSON plus CPU-only Simple | RPS, GPU hits, CPU fallbacks, device time, end-to-end latency |

### DB Server / DB Operators

| Workload | Simple Target | External Baselines | Metrics |
|---|---|---|---|
| OLAP scan/filter/project | Pure SQL + GPU columnar batch | ClickHouse/ClickBench, DuckDB, PostgreSQL where available | query time, rows/s, CPU/GPU time, correctness |
| Join/aggregate | Pure SQL join aggregate GPU validation | TPC-H-style Q1/Q3/Q5 subset, ClickBench aggregate queries | query time, fallback reason, row equality |
| NoSQL document filter | NoSQL document offload | YCSB-style scan/filter, Mongo-compatible local fixture if available | docs/s, p95, CPU/GPU hits |
| Vector search | vector store GPU batch | ANN-style local oracle fixture | queries/s, recall/correct IDs, GPU time |
| SSD-backed materialized scan | DBFS/NVFS materialized scan offload | ClickBench cold/hot run shape | cold/hot query time, WAL/durability CPU ownership |

## Required Harness Work

1. Extend `scripts/check/check-proxy-live-socket-benchmark.shs` or add a sibling
   wrapper that optionally runs installed external servers:
   `nginx`, `haproxy`, `envoy`, `caddy`, `h2o`, and a tiny C/Go/uWebSockets
   reference where available.
2. Normalize benchmark inputs:
   same payload bytes, same keep-alive policy, same connection count, same
   worker count, same logging policy, same CPU affinity where possible.
   HTTP report normalization is now materialized for the current `wrk` wrappers;
   future external wrappers must either use the same values or update the shared
   normalization section before claiming comparable results.
3. Use `wrk` or the existing Python socket harness for all HTTP rows. If `wrk`
   is unavailable, record `tool-unavailable:wrk` and keep current loopback
   harness rows only.
4. Add DB benchmark wrappers that map Simple datasets to standard shapes:
   ClickBench-inspired OLAP, TPC-H-style join/aggregate, BenchBase/YCSB-style
   transactional/key-value/document tests.
5. Record hardware and environment in every report: CPU model, cores,
   `nvidia-smi`/CUDA availability when present, kernel, RAM, storage, and
   Simple runtime mode.

## GPU Claim Rules

No benchmark row may claim GPU acceleration unless all are true:

- CPU oracle output matches the GPU candidate output.
- The dispatch target is a coarse web/DB batch, not HTTP parsing, TCP proxying,
  WAL, checkpoint, or invalidation.
- `gpu_hits > 0`, `cpu_fallbacks == 0`, and device timing source is valid.
- Tiny batches report CPU fallback instead of GPU success.
- Mismatch, stale generation, unsupported backend, timeout, or transfer failure
  produces a named fallback reason.

## Acceptance Gates

- `STATUS: PASS proxy live HttpServer reliable suite`
- `STATUS: PASS proxy live socket benchmark`
- `STATUS: PASS gpu web/db offload native device probe`
- `STATUS: PASS gpu web/db offload benchmark report`
- New external-comparison wrapper prints either `STATUS: PASS` with at least one
  Simple-vs-external row or `STATUS: WARN tool-unavailable` with explicit
  missing tools.
- New DB benchmark wrapper prints either `STATUS: PASS` with standard-shape DB
  rows or `STATUS: WARN tool-unavailable` with explicit missing tools.

## Implementation Order

1. Freeze the current reliable CPU proxy suite as the correctness gate.
2. Add external web-server benchmark wrapper with optional NGINX first, then
   HAProxy/Envoy/Caddy/H2O/uWebSockets as available. NGINX and the Caddy/H2O
   static-file producer paths are now materialized, and the HAProxy/Envoy cached
   proxy plus HAProxy upload/tunnel producers are materialized behind configured
   fixture URLs. The same producer now covers dynamic CPU/GPU plaintext and JSON
   route URL pairs plus optional uWebSockets/Seastar plaintext reference URL
   pairs.
3. Add `wrk`-based HTTP matrix rows for static, proxy, upload, tunnel, and
   dynamic GPU route shapes.
4. Add DB benchmark harness rows for ClickBench-inspired scans and TPC-H-style
   join/aggregate before NoSQL/vector expansion. The first live producer
   standard-shape manifest is now materialized in
   `scripts/check/check-gpu-web-db-offload-external-db-baselines.shs`; measured
   rows still require installed/configured DB baselines.
5. Add summary tables under `doc/10_metrics/perf/` and reports under
   `doc/09_report/perf/`.
6. Only after reproducible external rows exist, optimize hot Simple paths in
   this order: request allocation/copy removal, worker op dispatch, proxy
   buffer reuse/backpressure, DB batch admission, GPU transfer amortization.
   The first request allocation/copy slice is materialized in
   `src/lib/nogc_async_mut/http_server/worker.spl`: streamed request bodies no
   longer allocate a discarded fully buffered upstream request wire before
   switching to streaming headers and fragments.
   The first worker op dispatch slice is also materialized in the same worker:
   proxy body send/receive inflight checks and retry scheduling now share
   `worker_tracked_op_exists` instead of duplicating the op-array scan.
   The first proxy buffer/backpressure slice is materialized in
   `src/lib/nogc_async_mut/http_server/proxy.spl`: response preparation now
   appends through `async_proxy_append_pending_client_data` so unsent client
   bytes are preserved and budgeted instead of overwritten if the policy helper
   is called with pending downstream data.
   The DB batch admission slice is materialized in
   `src/lib/nogc_sync_mut/web_db_offload/queue.spl`: DB row/document/vector
   batches now produce a `GpuWdbDbBatchAdmission` decision before dispatch, and
   the benchmark report records accepted, queue-full fallback, and tiny-batch
   fallback outcomes.
   The GPU transfer amortization slice is also materialized in
   `src/lib/nogc_sync_mut/web_db_offload/queue.spl`: repeated logical GPU work
   can now report naive per-call transfer overhead versus one coalesced batch
   transfer, and the benchmark report records
   `gpu_transfer_amortization_policy_contract` with 3072 saved fixed-overhead
   bytes for four 8x2048 web transform calls.
   The DB external-baseline status slice is materialized in
   `test/05_perf/web_db_offload/gpu_web_db_offload_bench_spec.spl` and
   `scripts/check/check-gpu-web-db-offload-benchmark-report.shs`: ClickHouse,
   DuckDB, PostgreSQL, MongoDB/YCSB, Redis/Valkey, and ANN/vector baselines now
   have explicit `external-db-baseline` rows with unavailable, ready-unmeasured,
   or ready-measured reasons. They still make no speedup claim; measured rows
   only record external baseline latency through the strict
   `GPU_WDB_EXTERNAL_DB_BASELINE_OUTPUT` contract. The producer wrapper for that contract is
   `scripts/check/check-gpu-web-db-offload-external-db-baselines.shs`, which the
   GPU Web/DB benchmark report gate now runs automatically. The same report
   gate exposes `--self-test-external-db-measured-parser` so the strict parser
   can be verified without writing measured rows into the normal host report,
   while the producer wrapper exposes `--self-test` for non-mutating line-shape
   verification.

## Done Definition

This plan is done only when reports contain reproducible Simple-vs-external
rows for web/proxy and DB workloads, plus validated GPU-hit/fallback evidence.
Until then, the lane remains implementation in progress.
