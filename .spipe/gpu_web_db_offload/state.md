# Feature: GPU Web and DB Offload

## Raw Request

use spipe dev skill, off load process to gpu for thoughput and perf. improve web server, db server. 1. add full offloadable reverse proxy, to backed web process directly, 2. off load many logic to gpu in coarse grained in web and db. 3. db support ram only db and most gpu offload db. and ssd base but gpu accelerated. add nosql for gpu base db mode, reeearch deeply. use spark and normal llm and use agent teams for pherallel. see doc/01_research/lib/networking/reverse_proxy_gpu_boundary_2026-06-16.md

## Task Type

feature

## Refined Goal

Add a production-oriented Simple web/database acceleration architecture that implements CPU-owned reverse proxying and enables coarse-grained GPU offload for selected web and database workloads, including RAM-only, SSD-backed GPU-accelerated, and NoSQL/vector GPU database modes.

## Acceptance Criteria

- AC-1: Reverse proxy uses existing `ServerConfig.upstreams`, `LocationConfig.proxy_pass`, `UpstreamConfig`, and `UpstreamServer`.
- AC-2: Proxy locations use a worker-level streaming state machine, not a fully buffered synchronous content handler.
- AC-3: CPU workers own TCP accept, HTTP parsing, routing, proxy forwarding, backpressure, and response serialization.
- AC-4: GPU work is limited to coarse-grained web/database payload compute with CPU fallback.
- AC-5: DB support covers RAM-only, SSD-backed GPU-accelerated, and NoSQL/vector GPU database modes.
- AC-6: Reliability and CPU correctness gates come before GPU throughput claims.
- AC-7: SPipe specs discriminate GPU-hit from CPU fallback with real assertions.

## Scope Exclusions

- Do not make the GPU accept TCP, parse HTTP, own normal proxy forwarding, or replace DB durability/invalidation control paths.
- Do not claim production GPU speedup without baseline, fallback, and resource evidence.

## Phase

implementation-in-progress-recovered

## Log

- recovery: Recreated lane state after current checkout no longer contained prior gpu_web_db_offload artifacts.
- recovery: Current jj working copy reports unrelated unresolved conflicts in `.spipe/gpu_containers_unified/state.md` and `src/app/cli/query_lint.spl`; this lane does not resolve or edit those files.
- plan: Added `doc/03_plan/perf/gpu_web_db_offload_optimization_benchmark_plan.md`
  for the web/db server GPU-offload optimization benchmark program.
- plan: The benchmark plan defines NGINX, HAProxy, Envoy, Caddy/H2O,
  uWebSockets-style, TechEmpower/wrk-shaped HTTP comparisons and ClickBench,
  TPC-H, BenchBase/YCSB-style DB workload comparisons before any production
  speedup claim.
- plan: Updated `doc/03_plan/agent_tasks/gpu_web_db_offload_impl_status.md`
  to link the external-comparison plan and keep lane status as implementation
  in progress.
- evidence: Local benchmark tool availability check found `nginx` at
  `/usr/sbin/nginx` and `wrk` at `/usr/bin/wrk`; `haproxy`, `envoy`, `caddy`,
  and `h2o` are missing and must be represented as explicit
  `tool-unavailable:*` rows until installed.
- evidence: Simple-vs-NGINX static rows are measured on this host. Redis/Valkey
  key/value server coverage now exists as a status-only external baseline row
  and standard-shape manifest entry, but it is not measured yet. The lane must
  not claim Redis parity or speedup until a real measured producer/consumer
  contract and live fixture evidence exist.
- recovery: Crash-session continuation was traced to
  `/home/ormastes/.codex/sessions/2026/06/16/rollout-2026-06-16T04-07-18-019ece9c-bb30-76a1-952f-7233322187d1.jsonl`.
  The actionable current worktree state is now the benchmark plan plus the
  recovery/readiness harness artifacts, not the stale pre-implementation phase
  note below.
- implementation: Current benchmark continuation artifacts are
  `doc/03_plan/perf/gpu_web_db_offload_optimization_benchmark_plan.md`,
  `scripts/check/check-gpu-web-db-offload-recovery-harness-self-tests.shs`,
  `scripts/check/check-gpu-web-db-offload-external-fixture-readiness.shs`,
  `scripts/check/check-gpu-web-db-offload-external-db-baselines.shs`,
  `scripts/check/check-web-server-nginx-compare-report.shs`,
  `scripts/check/check-web-server-nginx-live-compare.shs`,
  `scripts/check/check-web-server-static-external-live-compare.shs`,
  `scripts/check/check-web-server-proxy-external-live-compare.shs`, and
  `scripts/check/check-web-server-dynamic-gpu-route-compare.shs`.
- evidence: Recovery harness self-test artifacts currently record 74 passed
  host-safe gates in
  `doc/09_report/perf/gpu_web_db_offload_recovery_harness_self_tests_2026-06-17.md`
  and `doc/10_metrics/perf/gpu_web_db_offload_recovery_harness_self_tests.md`.
- implementation: Added optional Caddy/H2O static external live producer. The
  wrapper emits strict measured rows when either tool is installed and exits
  cleanly with `STATUS: WARN tool-unavailable:caddy,h2o` on this host.
- implementation: Added optional HAProxy/Envoy cached proxy external live
  producer. The wrapper emits strict measured rows when cached proxy fixture
  URLs are configured and exits cleanly with
  `STATUS: WARN live-fixture-unavailable:proxy-external-urls-not-configured` on
  this host.
- implementation: Extended the proxy external live producer to consume
  `SIMPLE_UPLOAD_PROXY_URL`/`HAPROXY_UPLOAD_PROXY_URL` and
  `SIMPLE_TUNNEL_PROXY_URL`/`HAPROXY_TUNNEL_PROXY_URL`, emitting strict upload
  and tunnel measured rows when those fixtures are configured.
- implementation: Added cached proxy fixture URL handoff to external fixture
  readiness. `SIMPLE_CACHED_PROXY_URL`, `HAPROXY_CACHED_PROXY_URL`, and
  `ENVOY_CACHED_PROXY_URL` now appear in the env template, setup checklist,
  readiness report, and `proxy_fixture_urls` missing-category output.
- implementation: Added HAProxy upload-streaming and upgrade-tunnel fixture URL
  handoff to external fixture readiness. `SIMPLE_UPLOAD_PROXY_URL`,
  `HAPROXY_UPLOAD_PROXY_URL`, `SIMPLE_TUNNEL_PROXY_URL`, and
  `HAPROXY_TUNNEL_PROXY_URL` now appear in the env template, setup checklist,
  readiness report, and `proxy_fixture_urls` missing-category output.
- implementation: Connected the external DB baseline producer to the generated
  fixture env handoff. It sources
  `build/perf/gpu_web_db_offload/external-fixtures.env` by default, with
  `DB_FIXTURE_ENV_FILE` as an override for alternate DB fixture files.
- implementation: Tightened the external DB baseline producer status contract.
  Normal runs now print either `STATUS: PASS external DB baseline producer
  rows:N` or `STATUS: WARN tool-unavailable:external-db-baselines`.
- implementation: Extended the proxy external live producer to source the
  generated `build/perf/gpu_web_db_offload/external-fixtures.env` handoff and
  emit dynamic CPU/GPU plaintext and JSON measured rows when the matching URL
  pairs are configured.
- implementation: Strengthened the external DB baseline producer so live DB
  commands use named ClickBench-style scan/filter, TPC-H-style join/aggregate,
  and Mongo/YCSB-style document-filter query shapes instead of connection-only
  probes. The standard-shape manifest has a host-safe self-test.
- evidence: `scripts/check/check-gpu-web-db-offload-benchmark-report.shs` now
  embeds the producer's printable external DB standard-shape manifest in
  `doc/09_report/perf/gpu_web_db_offload_benchmark_2026-06-16.md` so report
  artifacts show the exact workload commands used by measured DB baselines.
- implementation: Aligned the standalone dynamic GPU route comparison wrapper
  with the shared external fixture env handoff. It now sources
  `build/perf/gpu_web_db_offload/external-fixtures.env` before reading
  `DYNAMIC_GPU_*` and `DYNAMIC_CPU_*` route URLs.
- implementation: Extended the generated external fixture env template with
  optional DB standard-shape query override variables. The DB baseline producer
  now reapplies default ClickBench/TPC-H/YCSB shapes after sourcing the env file,
  so blank template slots do not erase the standard workload commands.
- implementation: Added `scripts/check/check-gpu-web-db-offload-external-suite.shs`
  as the canonical ordered external-fixture suite runner. It writes handoff
  files, runs readiness, web/proxy/dynamic-route producers, DB producers and
  reports, then checks artifact consistency; `--dry-run` prints the sequence.
- verification: The recovery artifact consistency guard now asserts the external
  suite wrapper exists, is executable, and is referenced from the generated
  setup checklist.
- evidence: The external suite wrapper now writes durable plan artifacts at
  `doc/09_report/perf/gpu_web_db_offload_external_suite_2026-06-17.md` and
  `doc/10_metrics/perf/gpu_web_db_offload_external_suite.md`, capturing the
  ordered suite steps, current missing fixture categories, suite-step count,
  missing-fixture item count, fixture-readiness verdict, and readiness
  bootstrap status including `bootstrap_container_engine`. The suite report and
  metrics table also include a `Handoff Artifacts` section with direct paths to
  the generated fixture env file, setup checklist, bootstrap manifest,
  Compose/docker-run templates, env-fields TSV, blocker manifest TSV,
  env hints, runbook, next-actions file, persisted status JSON, readiness
  policy JSON, and missing-category files.
- evidence: `scripts/check/check-gpu-web-db-offload-external-suite.shs --status`
  prints the suite-step count, missing-fixture item count, and verdict directly.
  With the default generated `external-fixtures.env` template left blank, the
  current status reports 31 steps, 29 missing fixture items, 26 required
  missing items, 3 optional missing reference items, and
  `WAITING_ON_FIXTURES`.
  It also prints `external-suite-missing=<category>|...`
  rows for the current blocker categories and
  `external-suite-handoff=<name>|<path>` rows for generated handoff files. The
  status self-test now covers both blocked and all-fixtures-ready verdict paths
  plus handoff row output. The sibling `--status-json` command emits the same
  suite-step count, verdict, missing categories, and handoff paths as a compact
  JSON object for automation. `--write-status-json` persists that automation
  view at `build/perf/gpu_web_db_offload/external-suite-status.json`;
  `--write-policy-json` persists the required/optional readiness split at
  `build/perf/gpu_web_db_offload/external-suite-readiness-policy.json`.
- evidence: `scripts/check/check-gpu-web-db-offload-external-suite.shs --refresh-status`
  refreshes the missing-by-category handoff file before printing status, so
  fixture operators can re-check after installing tools or exporting URLs
  without relying on stale status artifacts.
- evidence: `scripts/check/check-gpu-web-db-offload-external-suite.shs --preflight`
  refreshes readiness and emits a final PASS/WARN line before a full external
  suite run; with the default blank fixture env it reports
  `STATUS: WARN ... missing:29`.
- implementation: The generated external fixture setup checklist now includes
  the external suite `--refresh-status` and `--preflight` commands before the
  full suite command, so fixture operators can re-check readiness without
  opening plan artifacts or launching live producers prematurely.
- implementation: The default external suite command now runs the preflight
  gate first and stops with a WARN status when fixture rows are missing. Use
  `--allow-partial` only for explicit local artifact refresh on hosts that are
  not fixture-ready; partial mode also ends with a WARN status so it cannot be
  confused with a fixture-ready full-suite PASS.
- implementation: Added external fixture readiness side-effect-free fixture
  setup writers: `--write-bootstrap-manifest`, `--write-docker-compose-template`,
  `--write-docker-run-template`, and `--write-proxy-config-templates`. They
  write the fixture manifest, compose template, Docker run fallback template,
  HAProxy config, and Envoy config without pulling images or starting services.
  The generated Compose and docker-run proxy fixtures map
  `host.docker.internal` to Docker's `host-gateway`, so Linux Docker hosts can
  reach the repo-local Simple proxy upstream without manually editing the
  proxy upstream address in the common local setup. The docker-run fallback is
  restart-safe for its generated fixture names: it removes and recreates only
  its own `gpu-web-db-*` containers. Bootstrap status detects both
  Docker Compose v2 (`docker compose`) and legacy `docker-compose` before
  reporting Compose as optional-missing, and prints `bootstrap_container_engine`
  so a present container CLI is not mistaken for a usable engine. The local
  fixture bootstrap summary reports `possible` only when that engine probe is
  ready; otherwise a present but unusable runtime reports `engine-unavailable`.
  The engine-status classifier has a host-safe self-test for ready,
  unavailable, missing, and unknown runtime states. The durable readiness
  report and metrics table include a separate `Bootstrap Status` section.
- implementation: External suite `--refresh-status` and `--preflight` now
  consume non-empty readiness URL values from
  `build/perf/gpu_web_db_offload/external-fixtures.env` when that file exists.
  Empty template assignments remain safe and do not erase exported variables or
  turn missing URL rows into ready rows. The env-file reader accepts bare
  `NAME=value`, `export NAME=value`, and simple quoted URL values for known
  readiness URL variables.
- implementation: Added a side-effect-free env-hints handoff:
  `scripts/check/check-gpu-web-db-offload-external-fixture-readiness.shs --write-env-hints`
  writes `build/perf/gpu_web_db_offload/external-fixture-env-hints.md` with
  commented localhost URL examples derived from the generated HAProxy, Envoy,
  ClickHouse, PostgreSQL, and MongoDB fixture templates. The external suite now
  includes this as the `write-env-hints` step.
- implementation: Added a side-effect-free operator runbook handoff:
  `scripts/check/check-gpu-web-db-offload-external-fixture-readiness.shs --write-runbook`
  writes `build/perf/gpu_web_db_offload/external-fixture-runbook.md` with the
  compose/proxy review step, env-file fill step, refresh/status/preflight
  commands, strict readiness gate, and guarded external suite command. The
  external suite now includes this as the `write-runbook` step.
- implementation: Added a side-effect-free next-actions handoff:
  `scripts/check/check-gpu-web-db-offload-external-fixture-readiness.shs --write-next-actions`
  writes `build/perf/gpu_web_db_offload/external-fixture-next-actions.md`,
  mapping the current missing categories to concrete operator actions. The
  external suite now includes this as the `write-next-actions` step and passes
  the same fixture env file used by refresh/preflight, so filled URL values are
  reflected consistently in the action map. The generated next-actions file
  records its missing-data source so operators can distinguish fixture-env-file
  handoff state from ambient environment state. It now includes a
  `Fixture Env Fields` table that maps missing URL-backed readiness items to
  the exact `external-fixtures.env` variables operators must fill.
- implementation: Added a side-effect-free env-fields TSV handoff:
  `scripts/check/check-gpu-web-db-offload-external-fixture-readiness.shs --write-env-fields`
  writes `build/perf/gpu_web_db_offload/external-fixture-env-fields.tsv`,
  a machine-readable readiness-item to env-variable map for fixture setup
  automation. The external suite now includes this as the `write-env-fields`
  step and advertises it through `external-suite-handoff=env_fields|...`.
- implementation: Added a side-effect-free blocker manifest handoff:
  `scripts/check/check-gpu-web-db-offload-external-fixture-readiness.shs --write-blocker-manifest`
  writes `build/perf/gpu_web_db_offload/external-fixture-blockers.tsv`,
  a machine-readable table combining missing category, readiness item, env
  variable when applicable, and next action. The external suite now includes
  this as the `write-blocker-manifest` step and advertises it through
  `external-suite-handoff=blocker_manifest|...`.
- documentation: Aligned
  `doc/03_plan/perf/gpu_web_db_offload_optimization_benchmark_plan.md` with the
  current 68-gate recovery harness and expanded `--check-current-artifacts`
  coverage, including the bootstrap manifest, Compose template, Docker run
  fallback, proxy configs, env-fields TSV, blocker manifest TSV, env hints,
  runbook, next-actions handoff, missing-by-category files, and external-suite
  status artifacts including persisted status JSON and readiness policy JSON.

## Selected Scope

Feature Options B and C selected. NFR selection: Reliability Options 1 and 2 first; then Performance Options 1, 2, and 3.

Next phase: keep the lane in implementation-progress until external fixtures
are installed/configured or provided by environment. Use
`scripts/check/check-gpu-web-db-offload-recovery-harness-self-tests.shs --check-current-artifacts`
as the fast crash-session continuation check before running heavier live
benchmark producers.
