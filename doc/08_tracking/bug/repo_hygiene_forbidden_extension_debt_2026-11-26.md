# Repo hygiene: forbidden-extension debt triage (2026-11-26)

**Status:** open. This is an owner-decision list.
**Gate:** `scripts/check/check-repo-hygiene.shs` (Repo Hygiene Regression Gate).
**Rule:** all code is `.spl`/`.shs`. No Python or Bash except the sanctioned bootstrap
scripts. CLAUDE.md § Critical Rules says "except 3 bootstrap scripts", and the gate
exempts 4: `bootstrap-from-scratch.sh`, `bootstrap-seed.sh`, `bootstrap-verify.sh`,
`build-phase3-phase4.sh`.

## Before

On `origin/release/1.0.0` at `1ca52709fb8`, the gate reported
`FAILED: 218 violation(s) found`:

- 212 forbidden-extension files that are not in the exact path/hash baseline;
- 5 "stale baseline" rows;
- 1 `numbered artifact changed-path audit failed`. That check is not part of the
  forbidden-extension class, it was already failing on the base, and it is
  tracked separately.

**The 5 stale rows are not files that are gone.** All 5 still exist, but their
content has changed since they were baselined (example:
`scripts/check/compiled-check-tree.py` is baselined as `ad2326…`, and its tree
hash is now `620d73…`). Each one therefore also shows up as a "new" row. Removing
the stale row alone fixes nothing. The row can only come out once the file itself
is deleted or ported. The baseline was not regenerated.

## Done in PR #11828

24 files were deleted. Each had zero references anywhere in the tree, no workflow
or glob runner invokes it, and it was last touched on or before 2026-11-22. The
list is in the PR body.

## Remaining, by category

The "refs" column counts tree files outside `doc/` that name the file by its full
basename. "Stem" means the file is mentioned only by its extensionless stem,
which is often a word match and not an invocation.

### (d) Sanctioned bootstrap tooling, exec'd by a sanctioned script

Policy: `.claude/rules/bootstrap.md` ("The lane **execs into `scripts/bootstrap/resume-stage3-from-admitted.sh`**") and `doc/07_guide/tooling/bootstrap_options.md`. These are POSIX `#!/bin/sh` with no bashisms found, so (b) rename-to-`.shs` is mechanically possible. But they are exec'd from `bootstrap-from-scratch.sh` and named in about 150 files, including tests, contracts and `config/bootstrap.sdn`, so the owner decides whether they move to `.shs` or join the sanctioned exemption.

| file | lines | note |
|---|---|---|
| `scripts/bootstrap/resume-stage2-from-cache.sh` | 326 | POSIX sh; stale baseline row (content changed) |
| `scripts/bootstrap/resume-stage3-from-admitted.sh` | 1592 | POSIX sh; stale baseline row (content changed) |
| `scripts/bootstrap/resume-stage4-from-admitted.sh` | 174 | POSIX sh; stale baseline row (content changed) |
| `scripts/bootstrap/lib/stage3-native-build-worker.sh` | 262 | POSIX sh; stale baseline row (content changed) |

### Live mail CLI (`tools/mail-cli/lib/*.bash`), real Bash, listed

This is the implementation behind the `mail` skill. All but `smtp.bash` and `pop3.bash` are over 150 lines.

| file | lines | note |
|---|---|---|
| `tools/mail-cli/lib/config.bash` | 597 | bash |
| `tools/mail-cli/lib/pop3.bash` | 66 | bash |
| `tools/mail-cli/lib/credentials.bash` | 127 | bash |
| `tools/mail-cli/lib/send.bash` | 262 | bash |
| `tools/mail-cli/lib/smtp.bash` | 46 | bash |
| `tools/mail-cli/lib/format.bash` | 364 | bash |
| `tools/mail-cli/lib/auth.bash` | 297 | bash |
| `tools/mail-cli/lib/inbox.bash` | 334 | bash |

### (c) Referenced tools, under 150 lines (port candidates)

| file | lines | refs |
|---|---|---|
| `src/runtime/test/check_enum_mixed_owner.sh` | 32 | bash with arrays; cited by ordinary_enum_checker_weak_owner_2026-10-05.md; Linux-ELF only, so it could not be verified on this Windows host |
| `test/fixtures/devhub/native_http_curl/verify_loopback.py` | 105 | 1 |
| `tools/upstream-skia-ganesh-vulkan/verify-skia-deps.py` | 111 | 1 |
| `scripts/check/check-windows-timestamp-providers.py` | 112 | 1 |
| `scripts/bootstrap/bounded-stream-live-adapter.py` | 119 | 1 |
| `scripts/check/lib/test-runner-source-routes.py` | 135 | 1 |
| `scripts/bootstrap/tests/phase-ladder-hello-test.py` | 148 | 1 |
| `scripts/check/check-windows-gnu-runtime-authority-test.py` | 28 | 1 |
| `test/fixtures/devhub/native_minio_binary_put/verify_health_cli.py` | 50 | 1 |
| `test/04_smoke/native_parent_parse_closure_scope_test.py` | 57 | 1 |
| `scripts/bootstrap/collect-diagnostic-continuation.py` | 58 | 1 |
| `scripts/check/check-git-archive-source-paths.py` | 59 | 1 |
| `scripts/check/check-seed-startup-test.py` | 64 | 1 |
| `scripts/check/check-simpleos-arm64-unified-firmware-contract.py` | 80 | 1 |
| `scripts/bootstrap/hello-sanity-buildrunner-worker.py` | 81 | 1 |
| `test/fixtures/devhub/native_minio_binary_put/verify_loopback.py` | 85 | 1 |
| `scripts/bootstrap/adaptive-executable-batch.py` | 97 | 1 |
| `scripts/check/check-seed-startup.py` | 56 | 2 |
| `scripts/bootstrap/hello-sanity-matrix-windows.py` | 60 | 2 |
| `scripts/bootstrap/capture-ladder-scv-evidence.py` | 68 | 2 |
| `scripts/check/check-windows-gnu-runtime-authority.py` | 71 | 2 |
| `scripts/bootstrap/hello-sanity-matrix-darwin.py` | 128 | 3 |
| `scripts/ci/prepare_mail_config_helper.py` | 134 | 3 |
| `scripts/bootstrap/phase1-terminal-gate.py` | 56 | 3 |
| `scripts/bootstrap/tool-code-authority.py` | 99 | 4 |
| `scripts/bootstrap/materialization-path-boundary.py` | 27 | 5 |

### (c) Referenced Python tools, 150 lines or more (listed, not ported)

| file | lines | refs |
|---|---|---|
| `scripts/bootstrap/collect-windows-phase2-objects.py` | 1342 | 1 |
| `scripts/check/replay-windows-ladder-providers.py` | 153 | 1 |
| `scripts/test/test-darwin-footprint-guard.py` | 172 | 1 |
| `test/fixtures/database/sqlcipher4/devhub1_crypto_oracle.py` | 178 | 1 |
| `scripts/bootstrap/materialize-source-packet.py` | 199 | 1 |
| `scripts/bootstrap/run-bootstrap-test-wave.py` | 203 | 1 |
| `test/fixtures/database/sqlite/gen_fixtures.py` | 214 | 1 |
| `scripts/bootstrap/tests/sanity-base-controls-test.py` | 234 | 1 |
| `scripts/bootstrap/tests/windows-collector-root-reap-test.py` | 242 | 1 |
| `scripts/bootstrap/owned_worker_wall_drain_windows.py` | 244 | 1 |
| `scripts/resource/freebsd-reaper-regression.py` | 650 | 1 |
| `scripts/bootstrap/tests/hello-sanity-buildrunner-receipt-test.py` | 661 | 1 |
| `scripts/check/lib/check-cold-hir-path-diagnostic.py` | 152 | 2 |
| `scripts/bootstrap/bounded-error-summary.py` | 179 | 2 |
| `scripts/check/lib/item5-hello-receipt.py` | 179 | 2 |
| `scripts/check/lib/bootstrap-stage3/sanity-base-controls.py` | 185 | 2 |
| `scripts/check/check-runtime-binary-size-matched-link.py` | 193 | 2 |
| `scripts/audit/unchanged-materialized-alias.py` | 242 | 2 |
| `scripts/check/diagnose_macos_existing_hostarch.py` | 242 | 2 |
| `test/fixtures/database/sqlcipher4/gen_dense_messenger_fixture.py` | 248 | 2 |
| `scripts/check/run-item5-matched-app-performance.py` | 256 | 2 |
| `scripts/check/rt-binding-index.py` | 271 | 2 |
| `scripts/check/lib/bootstrap-stage3/sanity-version-composition.py` | 291 | 2 |
| `scripts/check/compiled-check-tree.py` | 499 | 2 |
| `scripts/bootstrap/bootstrap-module-progress.py` | 153 | 3 |
| `scripts/bootstrap/hello-sanity-buildrunner.py` | 303 | 3 |
| `scripts/bootstrap/lib/stage3-cgroupfs.py` | 326 | 3 |
| `scripts/check/lib/stage4-retained-manual.py` | 791 | 3 |
| `test/fixtures/database/sqlcipher4/gen_sqlcipher4_fixture.py` | 549 | 4 |
| `scripts/bootstrap/phase1-whole-tests.py` | 204 | 5 |
| `scripts/check/lib/stage4-retained-self-evidence.py` | 299 | 5 |
| `scripts/check/check-rt-c-contract-compile.py` | 596 | 5 |
| `test/fixtures/devhub/fresh_secured_db/provision.py` | 312 | 7 |
| `scripts/check/check-rt-host-map.py` | 414 | 8 |
| `scripts/bootstrap/hello-sanity-matrix.py` | 920 | 8 |
| `scripts/check/check-rt-pointer-ref-map.py` | 506 | 9 |
| `scripts/bootstrap/run-process-group-bounded-log-windows.py` | 396 | 16 |

### Mentioned only in docs, or only by stem (likely dead; owner confirms)

| file | lines | why kept |
|---|---|---|
| `doc/01_research/domain/simple_clang_header_cache_2026-09-25/evidence/run_probes.py` | 190 | KEEP (2026-11-26, dead-rest lane): retained evidence script, cited by bug/research docs as provenance; deleting it breaks those links |
| `doc/08_tracking/bug/evidence/runtime_value_get_type_2026_11_14/run_probe.py` | 36 | KEEP (2026-11-26, dead-rest lane): retained evidence script, cited by bug/research docs as provenance; deleting it breaks those links |
| `doc/08_tracking/bug/evidence/target_profile_2026_11_14/cache_probe.py` | 35 | KEEP (2026-11-26, dead-rest lane): retained evidence script, cited by bug/research docs as provenance; deleting it breaks those links |
| `doc/08_tracking/bug/evidence/target_profile_2026_11_14/extract.py` | 37 | KEEP (2026-11-26, dead-rest lane): retained evidence script, cited by bug/research docs as provenance; deleting it breaks those links |
| `doc/08_tracking/bug/evidence/target_profile_2026_11_14/formal-stages1-3.sh` | 124 | KEEP (2026-11-26, dead-rest lane): retained formal-gate evidence, linked by compile_target_profile_optimization_coupling_2026_11_14.md; deleting it breaks provenance |
| `doc/08_tracking/bug/evidence/target_profile_2026_11_14/run_probe.py` | 36 | KEEP (2026-11-26, dead-rest lane): retained evidence script, cited by bug/research docs as provenance; deleting it breaks those links |
| `scripts/bootstrap/cache-identity-model-check.py` | 128 | cited only from doc/ or the baseline |
| `scripts/bootstrap/lib/executable_batch_policy.py` | 95 | cited only from doc/ or the baseline |
| `scripts/bootstrap/tests/archive-root-exclusions-test.py` | 82 | deleted 2026-11-26: no live reference (docs-only or none); never run by CI |
| `scripts/bootstrap/tests/authority-generation-retention-test.py` | 109 | deleted 2026-11-26: no live reference (docs-only or none); never run by CI |
| `scripts/bootstrap/tests/bootstrap-test-wave-test.py` | 168 | zero-ref test; may test live code |
| `scripts/bootstrap/tests/bounded-error-summary-test.py` | 84 | deleted 2026-11-26: no live reference (docs-only or none); never run by CI |
| `scripts/bootstrap/tests/bounded-live-diagnostics-test.py` | 198 | deleted 2026-11-26: no live reference (docs-only or none); never run by CI |
| `scripts/bootstrap/tests/collect-windows-phase2-objects-test.py` | 255 | deleted 2026-11-26: no live reference (docs-only or none); never run by CI |
| `scripts/bootstrap/tests/executable-batch-lease-test.py` | 39 | cited only from doc/ or the baseline |
| `scripts/bootstrap/tests/executable-batch-owner-test.py` | 61 | cited only from doc/ or the baseline |
| `scripts/bootstrap/tests/executable-batch-test.py` | 25 | cited only from doc/ or the baseline |
| `scripts/bootstrap/tests/freebsd-command-telemetry-test.py` | 211 | deleted 2026-11-26: no live reference (docs-only or none); never run by CI |
| `scripts/bootstrap/tests/full-inventory-selection-test.py` | 92 | deleted 2026-11-26: no live reference (docs-only or none); never run by CI |
| `scripts/bootstrap/tests/hello-sanity-matrix-env-test.py` | 77 | deleted 2026-11-26: no live reference (docs-only or none); never run by CI |
| `scripts/bootstrap/tests/host-gpu-provider-contract-test.py` | 151 | deleted 2026-11-26: no live reference (docs-only or none); never run by CI |
| `scripts/bootstrap/tests/ladder-seed-runtime-retention-test.py` | 111 | deleted 2026-11-26: no live reference (docs-only or none); never run by CI |
| `scripts/bootstrap/tests/materialization-path-boundary-bench.py` | 97 | deleted 2026-11-26: no live reference (docs-only or none); never run by CI |
| `scripts/bootstrap/tests/materialization-path-boundary-memory-test.py` | 35 | deleted 2026-11-26: no live reference (docs-only or none); never run by CI |
| `scripts/bootstrap/tests/materialization-path-boundary-test.py` | 57 | deleted 2026-11-26: no live reference (docs-only or none); never run by CI |
| `scripts/bootstrap/tests/materialize-source-packet-test.py` | 152 | deleted 2026-11-26: no live reference (docs-only or none); never run by CI |
| `scripts/bootstrap/tests/module-progress-test.py` | 143 | deleted 2026-11-26: no live reference (docs-only or none); never run by CI |
| `scripts/bootstrap/tests/phase1-whole-jobs-test.py` | 136 | deleted 2026-11-26: no live reference (docs-only or none); never run by CI |
| `scripts/bootstrap/tests/phase1-whole-json-command-test.py` | 80 | deleted 2026-11-26: no live reference (docs-only or none); never run by CI |
| `scripts/bootstrap/tests/phase1-whole-stream-test.py` | 47 | zero-ref test; may test live code |
| `scripts/bootstrap/tests/phase1-whole-tests-test.py` | 74 | deleted 2026-11-26: no live reference (docs-only or none); never run by CI |
| `scripts/bootstrap/tests/phase-ladder-hello-windows-test.py` | 73 | deleted 2026-11-26: no live reference (docs-only or none); never run by CI |
| `scripts/bootstrap/tests/phase-ladder-prior-failure-test.py` | 39 | zero-ref test; may test live code |
| `scripts/bootstrap/tests/phase-ladder-resume-test.py` | 262 | deleted 2026-11-26: no live reference (docs-only or none); never run by CI |
| `scripts/bootstrap/tests/phase-ladder-strict-seed-test.py` | 365 | cited only from doc/ or the baseline |
| `scripts/bootstrap/tests/phase-ladder-windows-runtime-test.py` | 38 | zero-ref test; may test live code |
| `scripts/bootstrap/tests/product-first-case-test.py` | 59 | deleted 2026-11-26: no live reference (docs-only or none); never run by CI |
| `scripts/bootstrap/tests/product-generated-snapshot-test.py` | 152 | deleted 2026-11-26: no live reference (docs-only or none); never run by CI |
| `scripts/bootstrap/tests/repository-native-row-test.py` | 90 | deleted 2026-11-26: no live reference (docs-only or none); never run by CI |
| `scripts/bootstrap/tests/repository-test-order-test.py` | 58 | deleted 2026-11-26: no live reference (docs-only or none); never run by CI |
| `scripts/bootstrap/tests/stage2-canonical-handoff-delegation-test.py` | 92 | deleted 2026-11-26: no live reference (docs-only or none); never run by CI |
| `scripts/bootstrap/tests/stage2-frontend-continuation-test.py` | 213 | deleted 2026-11-26: no live reference (docs-only or none); never run by CI |
| `scripts/bootstrap/tests/stage3-focused-composition-binding-test.py` | 83 | deleted 2026-11-26: no live reference (docs-only or none); never run by CI |
| `scripts/bootstrap/tests/stage3-focused-provenance-test.py` | 308 | deleted 2026-11-26: no live reference (docs-only or none); never run by CI |
| `scripts/bootstrap/tests/stage3-invocation-consistency-test.py` | 81 | deleted 2026-11-26: no live reference (docs-only or none); never run by CI |
| `scripts/bootstrap/tests/stage3-source-policy-test.py` | 152 | deleted 2026-11-26: no live reference (docs-only or none); never run by CI |
| `scripts/bootstrap/tests/stage3-worker-lowering-lane-test.py` | 120 | deleted 2026-11-26: no live reference (docs-only or none); never run by CI |
| `scripts/bootstrap/tests/subsystem-product-resume-test.py` | 148 | deleted 2026-11-26: no live reference (docs-only or none); never run by CI |
| `scripts/bootstrap/tests/tool-code-authority-test.py` | 132 | deleted 2026-11-26: no live reference (docs-only or none); never run by CI |
| `scripts/bootstrap/tests/tool-validator-import-test.py` | 33 | deleted 2026-11-26: no live reference (docs-only or none); never run by CI |
| `scripts/bootstrap/tests/watchdog-source-path-test.py` | 190 | deleted 2026-11-26: no live reference (docs-only or none); never run by CI |
| `scripts/bootstrap/tests/windows-collector-zero-timeout-test.py` | 107 | deleted 2026-11-26: no live reference (docs-only or none); never run by CI |
| `scripts/bootstrap/tests/windows-output-root-env-test.py` | 80 | cited only from doc/ or the baseline |
| `scripts/check/assemble-parse-closure-native-probe.py` | 46 | cited only from doc/ or the baseline |
| `scripts/check/check-arm64-boot-dtb-handoff.py` | 254 | cited only from doc/ or the baseline |
| `scripts/check/check-arm64-net-tx-ring-cursor.py` | 141 | cited only from doc/ or the baseline |
| `scripts/check/check-arm64-wm-firmware-image.py` | 97 | cited only from doc/ or the baseline |
| `scripts/check/check-bootstrap-cargo-path-batch.py` | 120 | cited only from doc/ or the baseline |
| `scripts/check/check-bootstrap-path-access.py` | 103 | cited only from doc/ or the baseline |
| `scripts/check/check-bootstrap-positioned-authority.py` | 868 | cited only from doc/ or the baseline |
| `scripts/check/check-bug-claim-lock-owner.py` | 172 | cited only from doc/ or the baseline |
| `scripts/check/check-coff-partial-link.py` | 104 | cited only from doc/ or the baseline |
| `scripts/check/check-coff-projection.py` | 55 | zero-ref tool, touched after 2026-11-22 |
| `scripts/check/check-core-stdin-line.py` | 82 | cited only from doc/ or the baseline |
| `scripts/check/check-env-guard-materialized-aliases.py` | 280 | cited only from doc/ or the baseline |
| `scripts/check/check-focused-native-output.py` | 103 | cited only from doc/ or the baseline |
| `scripts/check/check-ladder-scv-evidence.py` | 84 | zero-ref tool, touched after 2026-11-22 |
| `scripts/check/check-materializer-startup-perf.py` | 184 | cited only from doc/ or the baseline |
| `scripts/check/check-mcp-script-mode-perf-contract.py` | 110 | cited only from doc/ or the baseline |
| `scripts/check/check-mir-immediate-diagnostic.py` | 62 | cited only from doc/ or the baseline |
| `scripts/check/check-office-handoff-evidence-root.py` | 77 | cited only from doc/ or the baseline |
| `scripts/check/check-owned-worker-drain-binding-windows.py` | 52 | cited only from doc/ or the baseline |
| `scripts/check/check-runner-self-coverage.py` | 60 | cited only from doc/ or the baseline |
| `scripts/check/check-rust-atomic-updates.py` | 53 | cited only from doc/ or the baseline |
| `scripts/check/check-stage2-scv-cold-init.py` | 114 | cited only from doc/ or the baseline |
| `scripts/check/check-windows-cross-caller.py` | 75 | cited only from doc/ or the baseline |
| `scripts/check/check-windows-cross-import-authority.py` | 90 | zero-ref tool, touched after 2026-11-22 |
| `scripts/check/check-windows-host-capacity.py` | 105 | cited only from doc/ or the baseline |
| `scripts/check/check-windows-private-root-sdk.py` | 52 | zero-ref tool, touched after 2026-11-22 |
| `scripts/check/check-windows-remove-tree.py` | 126 | cited only from doc/ or the baseline |
| `scripts/check/runtime-value-get-type-projection.py` | 81 | cited only from doc/ or the baseline |
| `scripts/check/target-profile-projection.py` | 37 | cited only from doc/ or the baseline |
| `scripts/check/test-item5-hello-receipt.py` | 219 | cited only from doc/ or the baseline |
| `scripts/check/test-item5-matched-app-performance.py` | 109 | zero-ref test; may test live code |
| `scripts/check/tests/cold_hir_path_diagnostic_contract_test.py` | 83 | cited only from doc/ or the baseline |
| `scripts/check/tests/test_prepush_selftest_isolation.py` | 85 | zero-ref test; may test live code |
| `scripts/check/test-stage4-retained-manual.py` | 515 | cited only from doc/ or the baseline |
| `scripts/debug/rsp_watch.py` | 172 | cited only from doc/ or the baseline |
| `scripts/release/tests/candidate-release-routing-test.py` | 140 | cited only from doc/ or the baseline |
| `scripts/test/test-arm32-authenticated-syscall-abi.py` | 187 | cited only from doc/ or the baseline |
| `scripts/test/test-hosted-cargo-working-directory.py` | 82 | cited only from doc/ or the baseline |
| `scripts/test/test-rss-observation-budget.py` | 36 | zero-ref test; may test live code |
| `scripts/test/test-rss-proc-stat-diagnostic.py` | 25 | cited only from doc/ or the baseline |
| `scripts/test/test-rss-proc-stat-record.py` | 91 | cited only from doc/ or the baseline |
| `test/00_quick/bootstrap/stage3_cgroupfs_kernel.py` | 127 | DECISION (d) keep: root-only Linux kernel regression for live scripts/bootstrap/lib/stage3-cgroupfs.py; not runnable or verifiable on this Windows host; follows the scripts/ lane decision on that helper |
| `test/00_unit/scripts/stage4_retained_self_evidence_test.py` | 219 | DECISION (d) keep: tests live scripts/check/lib/stage4-retained-self-evidence.py (scripts/ lane owns it); port or delete together with that helper |
| `test/01_unit/app/devhub/mail_cli_shared_config_test.bash` | 98 | DECISION (d) keep: tests live tools/mail-cli/lib/config.shs and auth.shs; real bash test, port is tracked by todo 467 with the mail CLI |
| `test/01_unit/runtime/windows_terminal_raw_bytes/project-controlled-provider.py` | 29 | DECISION (d) keep: builds the fault-injection provider for live rt_term_write (src/runtime/runtime_core_io_exports.c); rt_core_exports_behaviour_selfcheck.c has no short/zero/error write cases, so not superseded; needs a Windows C toolchain to port and verify |
| `test/01_unit/runtime/windows_terminal_raw_bytes/run-term-byte-fixtures.py` | 56 | DECISION (d) keep: runner for the provider above; port the pair together |
| `test/01_unit/scripts/bootstrap_cache_path_retention_test.py` | 38 | DECISION (c) PORTED to test/01_unit/scripts/bootstrap_cache_path_retention_spec.spl (passes; fails with stage3-native-cache renamed in the collector); original deleted |
| `test/01_unit/scripts/bootstrap_campaign_nested_session_test.py` | 28 | DECISION (d) keep: needs perl process-tree watchdog and real process sessions (Linux only); cannot verify on this host |
| `test/01_unit/scripts/bootstrap_essential_apps_gate_test.py` | 173 | DECISION (d) keep: 173 lines against live check-bootstrap-essential-apps.shs and validate-test-runner-json.pl; no sibling coverage; port is a separate lane |
| `test/01_unit/scripts/hello_sanity_buildrunner_test.py` | 287 | DECISION (d) keep: tests live scripts/bootstrap/hello-sanity-buildrunner.py; follows the scripts/ lane decision on that helper |
| `test/01_unit/scripts/hello_sanity_matrix_test.py` | 312 | DECISION (d) keep: tests live hello-sanity-matrix.py and hello-sanity-matrix-darwin.py; follows the scripts/ lane decision |
| `test/01_unit/scripts/native_aot_suite_contract_test.py` | 179 | DECISION (d) keep: 179 lines against live run-native-aot-suite.shs; sibling bootstrap_native_aot_evidence_contract_test.shs covers only the evidence validator, not the suite runner; port is a separate lane |
| `test/01_unit/scripts/reviewed_native_sanity_argv_test.py` | 76 | DECISION (c) PORTED to test/01_unit/scripts/reviewed_native_sanity_argv_spec.spl plus reviewed_native_sanity_argv_fixture.shs (passes; fails when the canonical argv gains a duplicate launcher name); original deleted |
| `test/01_unit/scripts/windows_collector_helper_hash_test.py` | 80 | DECISION (d) keep: tests live run-process-group-bounded-log-windows.py; follows the scripts/ lane decision on that helper |
| `test/01_unit/tools/mail_cli/account_secret_argv_test.bash` | 72 | DECISION (d) keep: tests live tools/mail-cli/lib/config.bash, which is itself baselined until the mail CLI port (todo 467) |
| `test/02_integration/app/fixtures/lsp_stdio_live_protocol_linux_evidence.py` | 41 | DECISION (d) keep: Linux evidence driver for the live simple_lsp_mcp server; needs an interactive stdio harness that process_run cannot provide |
| `test/02_integration/app/lsp_native_stdio_protocol_test.py` | 208 | DECISION (d) keep: live protocol gate (JSONL and Content-Length with stdin held open); no spec covers it and process_run cannot hold stdin open |
| `test/02_integration/app/mcp_native_stdio_protocol_test.py` | 30 | DECISION (d) keep: thin wrapper over lsp_native_stdio_protocol_test.py; moves with it |
| `test/fixtures/database/sqlcipher4/gen_boundary_oracles.py` | 24 | DECISION (d) keep: independent oracle (stdlib hashlib, by design not Simple) that is the provenance of checked-in boundary_oracles.sdn; porting would remove the independence |
| `test/scripts/test_prepare_mail_config_helper.py` | 52 | DECISION (b) already removed by 1586a6278f9 (helper ported to scripts/ci/prepare_mail_config_helper.shs); row was stale |

## Coordinator default decisions, applied 2026-11-26 (not owner-signed)

- **(d) bootstrap scripts:** the 4 files are now exempted in
  `scan_forbidden_extension_files` (same mechanism as the other bootstrap scripts), not renamed. Because they are
  no longer scanned, their baseline rows (`resume-stage2/3/4`) were removed. A re-sealed row
  would itself be reported stale once the path is exempt. The reason (bootstrap rule, `.claude/rules/bootstrap.md`) is recorded beside the
  exemption. `stage3-native-build-worker.sh` had no baseline row. CLAUDE.md and `bootstrap.md` updated.
- **Mail CLI `*.bash` (8 files):** baselined with exact hashes under the reason "mail skill runtime; port
  tracked in todo", time-boxed to 2027-01-31; todo 467 tracks the port. The gate does not enforce the date.
- **Likely-dead list (114 files above):** nothing deleted. Every row in the "Mentioned only in docs, or only by
  stem" table is recorded as **owner-review**.
- **CI:** the failing "Mail host fixtures" step is a missing producer variable, see
  `mail_cli_portability_producer_unset_2026-11-26.md`.
