# GPU Web/DB External Suite Metrics

| metric | value |
|---|---:|
| suite_steps | 25 |
| missing_fixture_items | 26 |
| missing_data_source | fixture-env-file:build/perf/gpu_web_db_offload/external-fixtures.env |
| strict_readiness_command | scripts/check/check-gpu-web-db-offload-external-suite.shs --require-ready |

## Handoff Artifacts

| artifact | path |
|---|---|
| fixture_env_file | `build/perf/gpu_web_db_offload/external-fixtures.env` |
| setup_checklist | `build/perf/gpu_web_db_offload/external-fixture-setup-checklist.md` |
| bootstrap_manifest | `build/perf/gpu_web_db_offload/external-fixture-bootstrap-manifest.tsv` |
| docker_compose_template | `build/perf/gpu_web_db_offload/external-fixture-compose.yaml` |
| docker_run_template | `build/perf/gpu_web_db_offload/external-fixture-docker-run.shs` |
| env_fields | `build/perf/gpu_web_db_offload/external-fixture-env-fields.tsv` |
| blocker_manifest | `build/perf/gpu_web_db_offload/external-fixture-blockers.tsv` |
| env_hints | `build/perf/gpu_web_db_offload/external-fixture-env-hints.md` |
| runbook | `build/perf/gpu_web_db_offload/external-fixture-runbook.md` |
| next_actions | `build/perf/gpu_web_db_offload/external-fixture-next-actions.md` |
| missing_by_category | `build/perf/gpu_web_db_offload/external-fixture-missing-by-category.env` |
| missing_by_category_source | `build/perf/gpu_web_db_offload/external-fixture-missing-by-category-source.env` |
| status_json | `build/perf/gpu_web_db_offload/external-suite-status.json` |
| policy_json | `build/perf/gpu_web_db_offload/external-suite-readiness-policy.json` |

## Bootstrap Status

| bootstrap check | status | reason |
|---|---|---|
| bootstrap_container_runtime | ready | docker:/usr/bin/docker |
| bootstrap_container_engine | ready | docker-info |
| bootstrap_package_manager | ready | apt:/usr/bin/apt |
| bootstrap_compose | optional-missing | docker-compose-not-installed |
| bootstrap_missing_fixture_items | info | 26 |
| bootstrap_local_fixture_bootstrap | possible | container-engine-ready |
| bootstrap_side_effects | none | status-only-no-install-no-container-start |

## Steps

| step | command |
|---|---|
| preflight | `scripts/check/check-gpu-web-db-offload-external-suite.shs --preflight` |
| write-env-template | `scripts/check/check-gpu-web-db-offload-external-fixture-readiness.shs --write-env-template` |
| write-setup-checklist | `scripts/check/check-gpu-web-db-offload-external-fixture-readiness.shs --write-setup-checklist` |
| bootstrap-status | `scripts/check/check-gpu-web-db-offload-external-fixture-readiness.shs --bootstrap-status` |
| write-bootstrap-manifest | `scripts/check/check-gpu-web-db-offload-external-fixture-readiness.shs --write-bootstrap-manifest` |
| write-docker-compose-template | `scripts/check/check-gpu-web-db-offload-external-fixture-readiness.shs --write-docker-compose-template` |
| write-docker-run-template | `scripts/check/check-gpu-web-db-offload-external-fixture-readiness.shs --write-docker-run-template` |
| write-proxy-config-templates | `scripts/check/check-gpu-web-db-offload-external-fixture-readiness.shs --write-proxy-config-templates` |
| write-env-fields | `scripts/check/check-gpu-web-db-offload-external-fixture-readiness.shs --write-env-fields` |
| write-blocker-manifest | `NEXT_ACTIONS_ENV_FILE=build/perf/gpu_web_db_offload/external-fixtures.env scripts/check/check-gpu-web-db-offload-external-fixture-readiness.shs --write-blocker-manifest` |
| write-env-hints | `scripts/check/check-gpu-web-db-offload-external-fixture-readiness.shs --write-env-hints` |
| write-runbook | `scripts/check/check-gpu-web-db-offload-external-fixture-readiness.shs --write-runbook` |
| write-next-actions | `NEXT_ACTIONS_ENV_FILE=build/perf/gpu_web_db_offload/external-fixtures.env scripts/check/check-gpu-web-db-offload-external-fixture-readiness.shs --write-next-actions` |
| write-missing-by-category | `scripts/check/check-gpu-web-db-offload-external-suite.shs --refresh-status` |
| write-status-json | `scripts/check/check-gpu-web-db-offload-external-suite.shs --write-status-json` |
| write-policy-json | `scripts/check/check-gpu-web-db-offload-external-suite.shs --write-policy-json` |
| readiness | `scripts/check/check-gpu-web-db-offload-external-fixture-readiness.shs` |
| nginx-live | `scripts/check/check-web-server-nginx-live-compare.shs` |
| static-external | `scripts/check/check-web-server-static-external-live-compare.shs` |
| proxy-external | `scripts/check/check-web-server-proxy-external-live-compare.shs` |
| dynamic-route | `scripts/check/check-web-server-dynamic-gpu-route-compare.shs` |
| web-report | `scripts/check/check-web-server-nginx-compare-report.shs` |
| db-baselines | `scripts/check/check-gpu-web-db-offload-external-db-baselines.shs` |
| db-report | `scripts/check/check-gpu-web-db-offload-benchmark-report.shs` |
| artifact-consistency | `scripts/check/check-gpu-web-db-offload-recovery-harness-self-tests.shs --check-current-artifacts` |
