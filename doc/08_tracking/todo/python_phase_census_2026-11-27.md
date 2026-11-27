# Python phase census (2026-11-27)

Policy (owner): Python only up to a built+verified Phase 2; p3+ is pure Simple. See `.claude/rules/bootstrap.md` "Python phase policy".

Scope: `git ls-files '*.py'` minus `vendor/` and `test/05_perf/fixtures/**` at `origin/release/1.0.0` `a4c98d2afb7`: **103 files**, plus `sdk-observer-evidence-v1.py` which landed after that tip (104). The task estimate of ~215 predates PR #11828 / `02cd694e250` and the 2026-11-26/27 port lanes. Companion tracker: `doc/08_tracking/bug/repo_hygiene_forbidden_extension_debt_2026-11-26.md`.

Phase rule: pre-p2 = seed build, stage2 build, stage2 admission / sanity / version admission, hello-sanity, phase1 test waves. p3+ = stage3/stage4, test runner, repo gates, test oracles, perf/dev tools. CI-run gates must get `.shs` twins (GitHub runners have no `bin/simple`).

Callers = tree files outside `doc/`, `*.md` and the hygiene baseline naming the basename or (for module imports) the stem.

## Counts

- ARCHIVE_EVIDENCE: 5
- BOTH: 3
- DEAD: 1
- DEAD_CANDIDATE: 9
- OWNED_HELLO_SANITY: 13
- P3_PLUS_ONLY: 32 (+1 sdk-observer, -1 durable_wal_fsync; 21 rows below moved to the four classes under it)
- INDEPENDENT_ORACLE: 9 (policy exception, stays Python)
- BLOCKED: 5 (see `python_test_oracle_piped_process_gaps_2026-11-27.md`)
- BENCHMARK_FIXTURE: 1 (kept)
- PERF_LANE: 6 (owned by the perf lane)
- PRE_P2_ONLY: 20

## Files

| file | class | callers | note |
|---|---|---|---|
| `build/review/p3fix-caret2-20261111-logs/devhub_interpreter_driver.py` | DEAD | - | tracked debris under build/review; zero references; deleted in this PR |
| `doc/01_research/domain/simple_clang_header_cache_2026-09-25/evidence/run_probes.py` | ARCHIVE_EVIDENCE | - | bug/research evidence script, not executed by any phase; owner decides archive vs delete |
| `doc/08_tracking/bug/evidence/runtime_value_get_type_2026_11_14/run_probe.py` | ARCHIVE_EVIDENCE | - | bug/research evidence script, not executed by any phase; owner decides archive vs delete |
| `doc/08_tracking/bug/evidence/target_profile_2026_11_14/cache_probe.py` | ARCHIVE_EVIDENCE | - | bug/research evidence script, not executed by any phase; owner decides archive vs delete |
| `doc/08_tracking/bug/evidence/target_profile_2026_11_14/extract.py` | ARCHIVE_EVIDENCE | - | bug/research evidence script, not executed by any phase; owner decides archive vs delete |
| `doc/08_tracking/bug/evidence/target_profile_2026_11_14/run_probe.py` | ARCHIVE_EVIDENCE | - | bug/research evidence script, not executed by any phase; owner decides archive vs delete |
| `scripts/audit/unchanged-materialized-alias.py` | P3_PLUS_ONLY | scripts/audit/direct-env-runtime-guard.shs | repo gate / test oracle / perf or dev tool (runs on p3+ toolchain) |
| `scripts/bench/checker-performance.py` | P3_PLUS_ONLY | test/01_unit/scripts/checker_performance_harness_test.shs | repo gate / test oracle / perf or dev tool (runs on p3+ toolchain) |
| `scripts/bootstrap/bootstrap-module-progress.py` | BOTH | scripts/bootstrap/bootstrap-phase-verification.shs | bootstrap-phase-verification.shs runs for p2 and p3/p4 |
| `scripts/bootstrap/bounded-error-summary.py` | PRE_P2_ONLY | - | seed/stage2/phase1 bootstrap path or its regression test (no caller: standalone test or unwired; owner review) |
| `scripts/bootstrap/bounded-stream-live-adapter.py` | PRE_P2_ONLY | - | seed/stage2/phase1 bootstrap path or its regression test (no caller: standalone test or unwired; owner review) |
| `scripts/bootstrap/collect-windows-phase2-objects.py` | PRE_P2_ONLY | - | seed/stage2/phase1 bootstrap path or its regression test (no caller: standalone test or unwired; owner review) |
| `scripts/bootstrap/hello-sanity-buildrunner-worker.py` | OWNED_HELLO_SANITY | scripts/bootstrap/hello-sanity-buildrunner.py | owned by hello-sanity lane (pre-p2 trust gates, hash-pinned); not touched here |
| `scripts/bootstrap/hello-sanity-buildrunner.py` | OWNED_HELLO_SANITY | scripts/bootstrap/hello-sanity-matrix.py scripts/bootstrap/tests/hello-sanity-buildrunner-receipt-test.py test/01_unit/scripts/hello_sanity_buildrunner_test.py | owned by hello-sanity lane (pre-p2 trust gates, hash-pinned); not touched here |
| `scripts/bootstrap/hello-sanity-matrix-darwin.py` | OWNED_HELLO_SANITY | scripts/bootstrap/hello-sanity-buildrunner.py scripts/bootstrap/hello-sanity-matrix.py test/01_unit/scripts/hello_sanity_matrix_test.py | owned by hello-sanity lane (pre-p2 trust gates, hash-pinned); not touched here |
| `scripts/bootstrap/hello-sanity-matrix-windows.py` | OWNED_HELLO_SANITY | scripts/bootstrap/hello-sanity-buildrunner.py scripts/bootstrap/hello-sanity-matrix.py | owned by hello-sanity lane (pre-p2 trust gates, hash-pinned); not touched here |
| `scripts/bootstrap/hello-sanity-matrix.py` | OWNED_HELLO_SANITY | scripts/bootstrap/hello-sanity-buildrunner-worker.py scripts/bootstrap/hello-sanity-buildrunner.py scripts/bootstrap/hello-sanity-matrix.shs +2 | owned by hello-sanity lane (pre-p2 trust gates, hash-pinned); not touched here |
| `scripts/bootstrap/lib/stage3-cgroupfs.py` | P3_PLUS_ONLY | scripts/bootstrap/resume-stage3-from-admitted.sh test/01_unit/scripts/process_tree_rss_bounded_diagnostic_test.shs | stage3/stage4 (p3+) path |
| `scripts/bootstrap/owned_worker_wall_drain_windows.py` | PRE_P2_ONLY | - | seed/stage2/phase1 bootstrap path or its regression test (no caller: standalone test or unwired; owner review) |
| `scripts/bootstrap/phase1-terminal-gate.py` | PRE_P2_ONLY | scripts/bootstrap/run-bootstrap-test-wave.py scripts/bootstrap/run-compiler-subsystem-test-products.shs scripts/bootstrap/tests/bootstrap-test-wave-test.py | seed/stage2/phase1 bootstrap path or its regression test |
| `scripts/bootstrap/phase1-whole-tests.py` | PRE_P2_ONLY | scripts/bootstrap/run-bootstrap-test-wave.py scripts/bootstrap/tests/phase1-whole-stream-test.py | seed/stage2/phase1 bootstrap path or its regression test |
| `scripts/bootstrap/run-bootstrap-test-wave.py` | PRE_P2_ONLY | scripts/bootstrap/tests/bootstrap-test-wave-test.py (stem import) | phase1 test wave; only its own test calls it (unwired; owner review) |
| `scripts/bootstrap/run-process-group-bounded-log-windows.py` | BOTH | scripts/bootstrap/bootstrap-logged-process.shs scripts/bootstrap/collect-windows-phase2-objects.py scripts/bootstrap/hello-sanity-buildrunner.py +12 | exec by bootstrap-logged-process.shs (all phases) and phase-ladder-step.shs |
| `scripts/bootstrap/tests/bootstrap-test-wave-test.py` | PRE_P2_ONLY | - | seed/stage2/phase1 bootstrap path or its regression test (no caller: standalone test or unwired; owner review) |
| `scripts/bootstrap/tests/hello-sanity-buildrunner-receipt-test.py` | OWNED_HELLO_SANITY | test/01_unit/app/bootstrap_builder/result_receipt_decode_spec.spl | owned by hello-sanity lane (pre-p2 trust gates, hash-pinned); not touched here |
| `scripts/bootstrap/tests/phase-ladder-hello-test.py` | PRE_P2_ONLY | - | seed/stage2/phase1 bootstrap path or its regression test (no caller: standalone test or unwired; owner review) |
| `scripts/bootstrap/tests/phase-ladder-prior-failure-test.py` | PRE_P2_ONLY | - | seed/stage2/phase1 bootstrap path or its regression test (no caller: standalone test or unwired; owner review) |
| `scripts/bootstrap/tests/phase-ladder-strict-seed-test.py` | PRE_P2_ONLY | - | seed/stage2/phase1 bootstrap path or its regression test (no caller: standalone test or unwired; owner review) |
| `scripts/bootstrap/tests/phase-ladder-windows-runtime-test.py` | PRE_P2_ONLY | - | seed/stage2/phase1 bootstrap path or its regression test (no caller: standalone test or unwired; owner review) |
| `scripts/bootstrap/tests/phase1-whole-stream-test.py` | PRE_P2_ONLY | - | seed/stage2/phase1 bootstrap path or its regression test (no caller: standalone test or unwired; owner review) |
| `scripts/bootstrap/tests/sanity-base-controls-test.py` | OWNED_HELLO_SANITY | .github/workflows/repo-hygiene.yml | owned by hello-sanity lane (pre-p2 trust gates, hash-pinned); not touched here |
| `scripts/bootstrap/tests/windows-collector-root-reap-test.py` | PRE_P2_ONLY | .github/workflows/repo-hygiene.yml | seed/stage2/phase1 bootstrap path or its regression test |
| `scripts/bootstrap/tests/windows-output-root-env-test.py` | PRE_P2_ONLY | - | seed/stage2/phase1 bootstrap path or its regression test (no caller: standalone test or unwired; owner review) |
| `scripts/bootstrap/tool-code-authority.py` | BOTH | scripts/bootstrap/lib/product-tool-authority.shs scripts/bootstrap/run-bootstrap-test-wave.py | product-tool-authority.shs (stage2 products and p3 tool products) |
| `scripts/build/tests/run-build-test.py` | P3_PLUS_ONLY | - | repo gate / test oracle / perf or dev tool (runs on p3+ toolchain) (no caller: unwired) |
| `scripts/check/check-bootstrap-phase-feature-matrix.py` | P3_PLUS_ONLY | test/01_unit/scripts/bootstrap_phase_feature_matrix_test.py | stage3/stage4 (p3+) path |
| `scripts/check/check-bootstrap-phase-live.py` | P3_PLUS_ONLY | scripts/bootstrap/stage4-tooling-matrix.shs test/01_unit/scripts/bootstrap_phase_live_test.py | stage3/stage4 (p3+) path |
| `scripts/check/check-coff-partial-link.py` | DEAD_CANDIDATE | - | no caller; repo_hygiene debt doc marks it owner-active (touched >=2026-11-23); left in place |
| `scripts/check/check-coff-projection.py` | DEAD_CANDIDATE | - | no caller; repo_hygiene debt doc marks it owner-active (touched >=2026-11-23); left in place |
| `scripts/check/check-focused-native-output.py` | DEAD_CANDIDATE | - | no caller; repo_hygiene debt doc marks it owner-active (touched >=2026-11-23); left in place |
| `scripts/check/check-rt-c-contract-compile.py` | P3_PLUS_ONLY | config/check/must_check_gates.sdn scripts/check/run-rt-map-checks.shs test/01_unit/app/check/rt_c_contract_compile_spec.spl | repo gate / test oracle / perf or dev tool (runs on p3+ toolchain) |
| `scripts/check/check-rt-host-map.py` | P3_PLUS_ONLY | .github/workflows/code-idiom-gates.yml config/check/must_check_gates.sdn scripts/check/check-rt-c-contract-compile.py +3 | repo gate / test oracle / perf or dev tool (runs on p3+ toolchain) |
| `scripts/check/check-rt-pointer-ref-map.py` | P3_PLUS_ONLY | .github/workflows/code-idiom-gates.yml config/check/must_check_gates.sdn scripts/check/check-rt-c-contract-compile.py +4 | repo gate / test oracle / perf or dev tool (runs on p3+ toolchain) |
| `scripts/check/check-runtime-binary-size-matched-link.py` | P3_PLUS_ONLY | scripts/check/check-runtime-binary-size-startup-cohort.shs test/01_unit/scripts/runtime_binary_size_startup_cohort_test.shs | repo gate / test oracle / perf or dev tool (runs on p3+ toolchain) |
| `scripts/check/check-windows-cross-caller.py` | DEAD_CANDIDATE | - | no caller; repo_hygiene debt doc marks it owner-active (touched >=2026-11-23); left in place |
| `scripts/check/check-windows-cross-import-authority.py` | DEAD_CANDIDATE | - | no caller; repo_hygiene debt doc marks it owner-active (touched >=2026-11-23); left in place |
| `scripts/check/check-windows-private-root-sdk.py` | DEAD_CANDIDATE | - | no caller; repo_hygiene debt doc marks it owner-active (touched >=2026-11-23); left in place |
| `scripts/check/classify-compiled-check-results.py` | DEAD_CANDIDATE | - | no caller; repo_hygiene debt doc marks it owner-active (touched >=2026-11-23); left in place |
| `scripts/check/compiled-check-tree.py` | P3_PLUS_ONLY | scripts/check/classify-compiled-check-results.py test/01_unit/scripts/compiled_check_tree_test.shs | repo gate / test oracle / perf or dev tool (runs on p3+ toolchain) |
| `scripts/check/diagnose_macos_existing_hostarch.py` | P3_PLUS_ONLY | .github/workflows/macos-existing-candidate-hostarch-diagnostic.yml .github/workflows/macos-phase23-evidence.yml | repo gate / test oracle / perf or dev tool (runs on p3+ toolchain) |
| `scripts/check/lib/bootstrap-stage3/sanity-base-controls.py` | OWNED_HELLO_SANITY | scripts/bootstrap/tests/sanity-base-controls-test.py scripts/check/lib/bootstrap-stage3/sanity.shs | owned by hello-sanity lane (pre-p2 trust gates, hash-pinned); not touched here |
| `scripts/check/lib/bootstrap-stage3/sanity-version-composition.py` | OWNED_HELLO_SANITY | scripts/bootstrap/resume-stage2-version-admission.shs scripts/check/lib/bootstrap-stage3/sanity.shs | owned by hello-sanity lane (pre-p2 trust gates, hash-pinned); not touched here |
| `scripts/check/lib/check-cold-hir-path-diagnostic.py` | P3_PLUS_ONLY | scripts/check/check-cold-hir-path-diagnostic.shs | repo gate / test oracle / perf or dev tool (runs on p3+ toolchain) |
| `scripts/check/lib/item5-hello-receipt.py` | OWNED_HELLO_SANITY | scripts/check/check-stage2-hello-world-native-build.shs | owned by hello-sanity lane (pre-p2 trust gates, hash-pinned); not touched here |
| `scripts/check/lib/stage4-retained-manual.py` | P3_PLUS_ONLY | scripts/bootstrap/bootstrap-phase-verification.shs scripts/check/lib/stage4-candidate-provenance.shs | stage3/stage4 (p3+) path |
| `scripts/check/lib/stage4-retained-self-evidence.py` | P3_PLUS_ONLY | scripts/bootstrap/bootstrap-phase-verification.shs scripts/check/lib/stage4-candidate-provenance.shs scripts/check/lib/stage4-retained-manual.py +1 | stage3/stage4 (p3+) path |
| `scripts/check/sdk-observer-evidence-v1.py` | P3_PLUS_ONLY | .github/workflows/sdk-worker-observer-cycle1.yml scripts/check/run-sdk-observer-cycle1.shs | CI evidence gate (landed after a4c98d2afb7); twin must be `.shs` |
| `scripts/check/qmp-send-virtio-input.py` | P3_PLUS_ONLY | scripts/check/check-simpleos-arm64-unified-live.shs scripts/check/check-simpleos-virtio-snd-qemu.shs test/01_unit/os/simpleos_arm64_unified_live_adapter_spec.spl +1 | repo gate / test oracle / perf or dev tool (runs on p3+ toolchain) |
| `scripts/check/replay-windows-ladder-providers.py` | P3_PLUS_ONLY | .github/workflows/windows-retained-provider-replay.yml scripts/check/guard_wiring_optout.txt | repo gate / test oracle / perf or dev tool (runs on p3+ toolchain) |
| `scripts/check/rt-binding-index.py` | P3_PLUS_ONLY | scripts/check/check-rt-c-contract-compile.py test/01_unit/app/check/rt_binding_index_spec.spl | repo gate / test oracle / perf or dev tool (runs on p3+ toolchain) |
| `scripts/check/run-item5-matched-app-performance.py` | OWNED_HELLO_SANITY | - | owned by hello-sanity lane (pre-p2 trust gates, hash-pinned); not touched here |
| `scripts/generate/public_suffix_idna_aliases.py` | P3_PLUS_ONLY | scripts/generate/generate-public-suffix-list.shs | repo gate / test oracle / perf or dev tool (runs on p3+ toolchain) |
| `scripts/resource/freebsd-reaper-regression.py` | P3_PLUS_ONLY | - | repo gate / test oracle / perf or dev tool (runs on p3+ toolchain) (no caller: unwired) |
| `scripts/test/test-arm32-authenticated-syscall-abi.py` | DEAD_CANDIDATE | - | no caller; repo_hygiene debt doc marks it owner-active (touched >=2026-11-23); left in place |
| `scripts/test/test-darwin-footprint-guard.py` | P3_PLUS_ONLY | - | repo gate / test oracle / perf or dev tool (runs on p3+ toolchain) (no caller: unwired) |
| `scripts/tool/renderdoc-qrenderdoc-python-smoke.py` | P3_PLUS_ONLY | scripts/tool/renderdoc-export-events.shs test/02_integration/tool/renderdoc_exporter_contract_test.shs | port blocked: runs inside qrenderdoc embedded Python |
| `scripts/tool/renderdoc-target-control-trigger.py` | P3_PLUS_ONLY | scripts/check/check-renderdoc-chrome-target-control.shs | repo gate / test oracle / perf or dev tool (runs on p3+ toolchain) |
| `scripts/tool/riscv64-unknown-elf-tool-wrapper.py` | P3_PLUS_ONLY | scripts/tool/riscv64-unknown-elf-gcc-wrapper.cmd scripts/tool/riscv64-unknown-elf-gxx-wrapper.cmd | dev toolchain wrapper (exec by .cmd shims) |
| `test/00_quick/bootstrap/stage3_cgroupfs_kernel.py` | P3_PLUS_ONLY | - | stage3/stage4 (p3+) path |
| `test/00_unit/scripts/stage4_retained_self_evidence_test.py` | P3_PLUS_ONLY | - | stage3/stage4 (p3+) path |
| `test/01_unit/runtime/windows_terminal_raw_bytes/project-controlled-provider.py` | BLOCKED | - | BLOCKED on python_test_oracle_piped_process_gaps_2026-11-27.md (holds child stdin open; needs piped stderr, byte-safe I/O, env on the piped path) |
| `test/01_unit/runtime/windows_terminal_raw_bytes/run-term-byte-fixtures.py` | BLOCKED | - | BLOCKED on python_test_oracle_piped_process_gaps_2026-11-27.md (holds child stdin open; needs piped stderr, byte-safe I/O, env on the piped path) |
| `test/01_unit/scripts/bootstrap_campaign_nested_session_test.py` | PRE_P2_ONLY | - | seed/stage2/phase1 bootstrap path or its regression test (no caller: standalone test or unwired; owner review) |
| `test/01_unit/scripts/bootstrap_essential_apps_gate_test.py` | PRE_P2_ONLY | - | seed/stage2/phase1 bootstrap path or its regression test (no caller: standalone test or unwired; owner review) |
| `test/01_unit/scripts/bootstrap_phase_feature_matrix_test.py` | P3_PLUS_ONLY | - | repo gate / test oracle / perf or dev tool (runs on p3+ toolchain) (no caller: unwired) |
| `test/01_unit/scripts/bootstrap_phase_live_test.py` | P3_PLUS_ONLY | - | repo gate / test oracle / perf or dev tool (runs on p3+ toolchain) (no caller: unwired) |
| `test/01_unit/scripts/hello_sanity_buildrunner_test.py` | OWNED_HELLO_SANITY | - | owned by hello-sanity lane (pre-p2 trust gates, hash-pinned); not touched here |
| `test/01_unit/scripts/hello_sanity_matrix_test.py` | OWNED_HELLO_SANITY | - | owned by hello-sanity lane (pre-p2 trust gates, hash-pinned); not touched here |
| `test/01_unit/scripts/native_aot_suite_contract_test.py` | PRE_P2_ONLY | - | seed/stage2/phase1 bootstrap path or its regression test (no caller: standalone test or unwired; owner review) |
| `test/01_unit/scripts/process_group_bounded_log_windows_test.py` | PRE_P2_ONLY | - | seed/stage2/phase1 bootstrap path or its regression test (no caller: standalone test or unwired; owner review) |
| `test/01_unit/scripts/windows_collector_helper_hash_test.py` | PRE_P2_ONLY | - | seed/stage2/phase1 bootstrap path or its regression test (no caller: standalone test or unwired; owner review) |
| `test/02_integration/app/fixtures/lsp_stdio_live_protocol_linux_evidence.py` | BLOCKED | - | BLOCKED on python_test_oracle_piped_process_gaps_2026-11-27.md (holds child stdin open; needs piped stderr, byte-safe I/O, env on the piped path) |
| `test/02_integration/app/lsp_native_stdio_protocol_test.py` | BLOCKED | - | BLOCKED on python_test_oracle_piped_process_gaps_2026-11-27.md (holds child stdin open; needs piped stderr, byte-safe I/O, env on the piped path) |
| `test/02_integration/app/mcp_native_stdio_protocol_test.py` | BLOCKED | - | BLOCKED on python_test_oracle_piped_process_gaps_2026-11-27.md (holds child stdin open; needs piped stderr, byte-safe I/O, env on the piped path) |
| `test/03_system/tools/jupyter/helpers/wrapper_transport_roundtrip.py` | P3_PLUS_ONLY | - | port blocked: exercises kernel_wrapper.py |
| `test/05_perf/startup/class_a/fixtures/class_a.py` | BENCHMARK_FIXTURE | scripts/check/check-startup-class-a-matrix.shs test/05_perf/startup/class_a/startup_class_a_schema_contract_test.shs | kept: the Python contestant of the cross-language startup matrix (siblings class_a.c/.rs/.go/.js/Java); porting destroys the benchmark |
| `test/fixtures/database/sqlcipher4/devhub1_crypto_oracle.py` | INDEPENDENT_ORACLE | test/02_integration/app/devhub/messenger/devhub1_oss_interop_spec.spl | independent oracle by design (non-Simple is the point); policy exception, stays Python; porting makes the spec compare Simple against Simple |
| `test/fixtures/database/sqlcipher4/gen_boundary_oracles.py` | INDEPENDENT_ORACLE | - | independent oracle by design (non-Simple is the point); policy exception, stays Python; porting makes the spec compare Simple against Simple |
| `test/fixtures/database/sqlcipher4/gen_dense_messenger_fixture.py` | INDEPENDENT_ORACLE | test/fixtures/database/sqlcipher4/dense_ground_truth.json test/support/devhub_messenger_dense.spl | independent oracle by design (non-Simple is the point); policy exception, stays Python; porting makes the spec compare Simple against Simple |
| `test/fixtures/database/sqlcipher4/gen_sqlcipher4_fixture.py` | INDEPENDENT_ORACLE | test/01_unit/lib/database/codec/sqlcipher4_independent_oracle_spec.spl test/01_unit/lib/database/server/storage_port_spec.spl test/02_integration/app/devhub/messenger/sqlcipher_messenger_e2e_spec.spl +1 | independent oracle by design (non-Simple is the point); policy exception, stays Python; porting makes the spec compare Simple against Simple |
| `test/fixtures/database/sqlite/gen_fixtures.py` | INDEPENDENT_ORACLE | test/01_unit/lib/database/sqlite_format/header_spec.spl | independent oracle by design (non-Simple is the point); policy exception, stays Python; porting makes the spec compare Simple against Simple |
| `test/fixtures/devhub/fresh_secured_db/provision.py` | INDEPENDENT_ORACLE | build/review/p3fix-caret1-20261111.sdn build/review/p3fix-caret2-20261111.sdn +4 | independent oracle by design (non-Simple is the point); policy exception, stays Python; porting makes the spec compare Simple against Simple |
| `test/fixtures/devhub/native_http_curl/verify_loopback.py` | INDEPENDENT_ORACLE | test/03_system/app/devhub/feature/minio_binary_put_spec.spl | independent oracle by design (non-Simple is the point); policy exception, stays Python; porting makes the spec compare Simple against Simple |
| `test/fixtures/devhub/native_minio_binary_put/verify_health_cli.py` | INDEPENDENT_ORACLE | test/03_system/app/devhub/feature/minio_binary_put_spec.spl | independent oracle by design (non-Simple is the point); policy exception, stays Python; porting makes the spec compare Simple against Simple |
| `test/fixtures/devhub/native_minio_binary_put/verify_loopback.py` | INDEPENDENT_ORACLE | test/03_system/app/devhub/feature/minio_binary_put_spec.spl | independent oracle by design (non-Simple is the point); policy exception, stays Python; porting makes the spec compare Simple against Simple |
| `test/perf/bench/durable_wal_fsync.py` | DEAD_CANDIDATE | - (mentioned by name in test/05_perf/bench/durable_wal_fsync.{shs,spl}, not exec'd) | superseded by the Simple bench twin; owner confirms before delete |
| `test/perf/dbserver/live_pgbench_compare.py` | PERF_LANE | test/perf/dbserver/test_live_pgbench_compare.py | owned by the perf lane (live compare harnesses); not ported by the test-oracle lane |
| `test/perf/dbserver/pgwire_smoke_client.py` | PERF_LANE | - | owned by the perf lane (live compare harnesses); not ported by the test-oracle lane |
| `test/perf/dbserver/test_live_pgbench_compare.py` | PERF_LANE | - | owned by the perf lane (live compare harnesses); not ported by the test-oracle lane |
| `test/perf/webserver/live_h2load_compare.py` | PERF_LANE | test/05_perf/webserver/live_h2load_compare.shs test/perf/webserver/test_live_h2load_compare.py | owned by the perf lane (live compare harnesses); not ported by the test-oracle lane |
| `test/perf/webserver/live_static_compare.py` | PERF_LANE | test/01_unit/perf/live_static_compare_contract_test.shs | owned by the perf lane (live compare harnesses); not ported by the test-oracle lane |
| `test/perf/webserver/test_live_h2load_compare.py` | PERF_LANE | - | owned by the perf lane (live compare harnesses); not ported by the test-oracle lane |
| `tools/jupyter/kernel_wrapper.py` | P3_PLUS_ONLY | scripts/test/jupyter-docker-test.shs test/03_system/tools/jupyter/helpers/wrapper_transport_roundtrip.py test/03_system/tools/jupyter/jupyter_kernel_install_system_spec.spl +5 | port blocked: Jupyter kernel protocol host is Python |
| `tools/jupyter/labextension/simple_labextension/__init__.py` | P3_PLUS_ONLY | - | port blocked: JupyterLab package shim |

## Follow-up PR plan

1. This PR: census, policy text, delete the single DEAD file.
2. P3_PLUS_ONLY ports by area (repo gates `check-rt-*` -> `.shs` for CI; test oracles / fixture generators; perf compares; stage3/stage4 helpers; dev tools). Host-embedded Python (`renderdoc-qrenderdoc`, Jupyter) is port-blocked and needs an owner exception.
3. BOTH twins: `run-process-group-bounded-log-windows`, `bootstrap-module-progress`, `tool-code-authority` (Python kept for pre-p2, `.spl`/`.shs` twin for p3+ callers).
4. DEAD_CANDIDATE / ARCHIVE_EVIDENCE rows need an owner call before deletion.

Each port/twin: TDD, parity on identical inputs (stdout, exit code, receipt bytes), runtime vs Python measured.
Related: `doc/08_tracking/bug/sanity_fresh_writer_pin_branch_skew_2026-11-27.md`.
