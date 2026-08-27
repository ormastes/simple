# Pure-Simple Tool and Infrastructure Hardening

> Qualifies the production Simple runtime and the developer-tool trust chain. The scenarios fail closed when the deployed runtime is a seed, a test result is greenwashed, CLI-controlled paths cross a shell, or launchers select source or debug fallbacks.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 5 | 5 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Pure-Simple Tool and Infrastructure Hardening

Qualifies the production Simple runtime and the developer-tool trust chain. The scenarios fail closed when the deployed runtime is a seed, a test result is greenwashed, CLI-controlled paths cross a shell, or launchers select source or debug fallbacks.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Requirements | REQ-001 through REQ-015 |
| Plan | doc/03_plan/sys_test/pure_simple_tool_infra_hardening.md |
| Design | doc/05_design/pure_simple_tool_infra_hardening.md |
| Research | doc/01_research/local/pure_simple_tool_infra_hardening.md |
| Source | `test/03_system/app/tooling/feature/pure_simple_tool_infra_hardening_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Qualifies the production Simple runtime and the developer-tool trust chain.
The scenarios fail closed when the deployed runtime is a seed, a test result is
greenwashed, CLI-controlled paths cross a shell, or launchers select source or
debug fallbacks.

**Requirements:** REQ-001 through REQ-015
**Plan:** doc/03_plan/sys_test/pure_simple_tool_infra_hardening.md
**Design:** doc/05_design/pure_simple_tool_infra_hardening.md
**Research:** doc/01_research/local/pure_simple_tool_infra_hardening.md

## Scenarios

### Pure-Simple tool and infrastructure hardening

#### REQ-001 REQ-002 REQ-011 NFR-003 NFR-011 NFR-012 admits only a truthful production runtime and inventory

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- REQ-001 REQ-002 REQ-011 NFR-003 NFR-011 NFR-012 admits only a truthful production runtime and inventory
- Admit a pure-Simple production runtime
   - Expected: qualification_runtime_identity() equals `pure-simple`
   - Expected: rollback_code equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 27 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("REQ-001 REQ-002 REQ-011 NFR-003 NFR-011 NFR-012 admits only a truthful production runtime and inventory")
step("Admit a pure-Simple production runtime")
expect(qualification_runtime_identity()).to_equal("pure-simple")
expect(qualification_source_contract(
    "scripts/setup/setup.shs",
    ["candidate_frontend_admission"],
    []
)).to_equal("safe")
expect(qualification_source_contract(
    "scripts/bootstrap/bootstrap-from-scratch.sh",
    ["deploy_simple_binary_atomically \"${full_bin}\" \"${deployed_bin}\"", "rm -f \"${deploy_dir}/simple_seed${exe_suffix}\"", "mcp_hash_tmp"],
    ["install -m755 \"${full_bin}\" \"${deployed_bin}\"", "Installed current seed delegate"]
)).to_equal("safe")
expect(qualification_source_contract(
    "scripts/check/cert/redeploy_gate/candidate_frontend_admission.shs",
    ["deploy_simple_binary_atomically() (", "retained_previous", "trap cleanup_deploy_transaction 0", "mv \"$deploy_tmp\" \"$live\"", "simple_binary_is_valid \"$live\"", "mv \"$restore_tmp\" \"$live\""],
    []
)).to_equal("safe")
val (_rollback_out, _rollback_err, rollback_code) = rt_process_run_timeout(
    "sh", ["scripts/check/check-deploy-rollback-contract.shs"], 30000)
expect(rollback_code).to_equal(0)
expect(qualification_source_contract(
    "src/app/cli/dispatch.spl",
    ["get_command_table"],
    ["g_command_count = 53", "g_simple_impl_count = 53"]
)).to_equal("safe")
```

</details>

#### REQ-003 through REQ-006 REQ-009 REQ-010 REQ-014 NFR-002 NFR-004 preserves developer-tool failures

- REQ-003 through REQ-006 REQ-009 REQ-010 REQ-014 NFR-002 NFR-004 preserves developer-tool failures
- Run truth-preserving developer tools
   - Expected: qualification_exit_class(0) equals `pass`
   - Expected: qualification_exit_class(1) equals `assertion_failure`
   - Expected: qualification_exit_class(2) equals `usage_error`
   - Expected: qualification_exit_class(3) equals `internal_error`
   - Expected: qualification_exit_class(4) equals `empty_discovery`
   - Expected: qualification_exit_class(124) equals `timeout_resource`
   - Expected: outcome_code equals `0`
   - Expected: fix_code equals `0`
   - Expected: qualification_termination_probe() equals `safe`


<details>
<summary>Executable SSpec</summary>

Runnable source: 174 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("REQ-003 through REQ-006 REQ-009 REQ-010 REQ-014 NFR-002 NFR-004 preserves developer-tool failures")
step("Run truth-preserving developer tools")
expect(qualification_no_placeholders(
    "test/03_system/app/tooling/feature/pure_simple_tool_infra_hardening_spec.spl"
)).to_equal("safe")
expect(qualification_source_contract(
    "src/lib/nogc_sync_mut/test_runner/test_executor_parsing.spl",
    ["exit_code != 0", "timeout"],
    ["elif exit_code != 0 and passed == 0"]
)).to_equal("safe")
expect(qualification_source_contract(
    "src/lib/nogc_sync_mut/test_runner/test_runner_async.spl",
    ["install_signal_handlers", "signal_dispatch_pending()", "cleanup_all_children"],
    []
)).to_equal("safe")
expect(qualification_source_contract(
    "src/lib/nogc_sync_mut/io/signal_stubs.spl",
    ["rt_signal_install(signal)", "installed <= 0", "_signal_handlers[i] = (signal, handler)"],
    ["_signal_handlers.push((signal, handler))\n    rt_signal_install"]
)).to_equal("safe")
expect(qualification_source_contract(
    "src/lib/nogc_sync_mut/test_runner/process_tracker.spl",
    ["else:\n                surviving.push(pid)"],
    []
)).to_equal("safe")
expect(qualification_source_contract(
    "src/app/test_runner_new/test_runner_client.spl",
    ["SIMPLE_TEST_DAEMON_CHILD", "--no-session-daemon", "process_spawn_async", "[\"-0\", pid]", "if not atomic_write_text"],
    ["src/compiler_rust/target/debug/simple", "[\"-c\", \"pid=$(cat", "rt_file_write_text(path, content)"]
)).to_equal("safe")
expect(qualification_source_contract(
    "src/app/test_runner_new/test_runner_main.spl",
    ["process_run_timeout(binary, child_args", "TimeoutResourceFailure", "test_batch_result_matches_manifest(batch_files, batch_result)"],
    ["process_run(binary, child_args"]
)).to_equal("safe")
expect(qualification_source_contract(
    "src/lib/nogc_sync_mut/io/process_ops.spl",
    ["1 + (timeout_ms - 1) / 1000", r"exec timeout --kill-after=5s {timeout_sec}s {full_cmd}"],
    ["timeout_buffer", "timeout_sec + 5"]
)).to_equal("safe")
expect(qualification_source_contract(
    "src/lib/nogc_sync_mut/daemon_sdk/client.spl",
    ["fn daemon_poll_attempt_limit(timeout_ms: i64) -> i64:", "2 + ((timeout_ms - 1) / 100)", "while rt_time_now_unix_micros() < deadline and attempts < daemon_poll_attempt_limit(timeout_ms):"],
    ["attempts < 600"]
)).to_equal("safe")
expect(qualification_source_contract(
    "src/app/test_dep_graph_shared.spl",
    ["extract_transitive_deps(module_path)", "seen[file_path] = true"],
    ["extract_transitive_deps(module_path, 5)", "pending_depths"]
)).to_equal("safe")
expect(qualification_source_contract(
    "src/compiler/90.tools/verify/lake_runner.spl",
    ["timeout_ms: i64", "shell_timeout(", "self.timeout_ms"],
    ["val result = shell("]
)).to_equal("safe")
expect(qualification_source_contract(
    "src/compiler/90.tools/verify/checker.spl",
    ["LakeRunner.new(config.project_dir, config.timeout_ms)"],
    ["LakeRunner.new(config.project_dir)"]
)).to_equal("safe")
expect(qualification_source_contract(
    "src/app/io/cli_lint_commands.spl",
    ["fn cli_run_lint", "fn cli_run_fmt", "fn cli_run_fix", "lint_source", "if run_repo_gates:", "check-ui-backend-isolation.shs", "check-cpu-hotloop-idiom.shs", "--mcp-perf is unavailable until its repository scanner has a production owner"],
    ["file_allows_lint", "[\"build\", \"lint\", \"--mcp-perf\"]"]
)).to_equal("safe")
expect(qualification_source_contract(
    "src/app/io/_CliCommands/run_commands.spl",
    [],
    ["fn cli_run_lint", "fn cli_run_fmt", "fn cli_run_fix"]
)).to_equal("safe")
expect(qualification_source_contract(
    "src/lib/nogc_sync_mut/spec.spl",
    ["SIMPLE_TEST_RESULT_FILE", "simple-bdd-v1", "_write_test_result_evidence()"],
    []
)).to_equal("safe")
expect(qualification_source_contract(
    "src/lib/nogc_sync_mut/test_runner/test_executor_parsing.spl",
    ["read_structured_test_evidence", "make_result_from_structured_evidence", "simple-bdd-v1", "structured BDD evidence is unavailable for this execution mode"],
    []
)).to_equal("safe")
expect(qualification_source_contract(
    "src/app/test_runner_new/test_runner_single.spl",
    ["read_test_result_evidence", "SIMPLE_TEST_RESULT_FILE", "simple-bdd-v1"],
    []
)).to_equal("safe")
expect(qualification_source_contract(
    "src/app/io/_CliCommands/handler_commands.spl",
    ["--test-result-file=", "SIMPLE_TEST_RESULT_FILE"],
    []
)).to_equal("safe")
expect(qualification_source_contract(
    "src/lib/nogc_sync_mut/test_runner/test_runner_execute.spl",
    ["--test-result-file={evidence_path}", "make_result_from_structured_evidence", "file_delete(evidence_path)"],
    []
)).to_equal("safe")
expect(qualification_source_contract(
    "src/compiler/90.tools/lint/_LintMain/entry_and_fixes.spl",
    ["--fix-dry-run", "file_atomic_write", "apply_collected_fixes"],
    []
)).to_equal("safe")
expect(qualification_source_contract(
    "src/compiler/90.tools/formatter/main.spl",
    ["file_atomic_write", "if not file_atomic_write(path, content)"],
    ["if not file_write(path, content)"]
)).to_equal("safe")
expect(qualification_source_contract(
    "src/runtime/runtime_native.c",
    ["rt_file_atomic_write(int64_t path_value", "O_EXCL", "fchmod(fd, existing_stat.st_mode", "fsync(fd)", "rename(temp_path, path)"],
    []
)).to_equal("safe")
expect(qualification_source_contract(
    "src/lib/nogc_sync_mut/io/file_ops.spl",
    ["rt_file_atomic_write(path, content)"],
    ["fn file_atomic_write(path: text, content: text) -> bool:\n    file_delete(path)"]
)).to_equal("safe")
expect(qualification_source_contract(
    "src/app/io/file_ops.spl",
    ["rt_file_atomic_write(path, content)"],
    ["fn file_atomic_write(path: text, content: text) -> bool:\n    file_write(path, content)"]
)).to_equal("safe")
expect(qualification_source_contract(
    "src/lib/nogc_async_mut/io/mod_stub.spl",
    ["rt_file_atomic_write(path, content)"],
    ["fn file_atomic_write(path: text, content: text) -> bool:\n    file_write(path, content)"]
)).to_equal("safe")
expect(qualification_source_contract(
    "src/compiler_rust/compiler/src/interpreter_extern/file_io.rs",
    ["NamedTempFile::new_in(parent)", "set_permissions(permissions)", "sync_all()", "temp.persist(path)"],
    []
)).to_equal("safe")
expect(qualification_source_contract(
    "src/compiler_rust/native_all/src/lib.rs",
    ["NamedTempFile::new_in(parent)", "set_permissions(permissions)", "sync_all()", "temp.persist(path)"],
    []
)).to_equal("safe")
expect(qualification_source_contract(
    "test/01_unit/runtime/runtime_native_focus_test.c",
    ["rt_file_atomic_write(text(atomic_path)", "replacement", "missing_path"],
    []
)).to_equal("safe")
expect(qualification_exit_class(0)).to_equal("pass")
expect(qualification_exit_class(1)).to_equal("assertion_failure")
expect(qualification_exit_class(2)).to_equal("usage_error")
expect(qualification_exit_class(3)).to_equal("internal_error")
expect(qualification_exit_class(4)).to_equal("empty_discovery")
expect(qualification_exit_class(124)).to_equal("timeout_resource")
val (_outcome_out, _outcome_err, outcome_code) = rt_process_run_timeout(
    "sh", ["scripts/check/check-test-runner-outcome-exits.shs"], 30000)
expect(outcome_code).to_equal(0)
expect(qualification_source_contract(
    "scripts/check/check-test-runner-outcome-exits.shs",
    ["kill -INT \"$RUNNER_PID\"", "signal_exit", "signal child survived cleanup"],
    []
)).to_equal("safe")
expect(qualification_source_contract(
    "src/app/gen_lean/main.spl",
    ["process_run_timeout", "src/compiler/90.tools/verify/main.spl"],
    ["[\"gen-lean\"]"]
)).to_equal("safe")
expect(qualification_source_contract(
    "src/compiler/90.tools/verify/main.spl",
    ["get_cli_args()", "val command = argv[0]"],
    ["get_args()", "val command = argv[1]"]
)).to_equal("safe")
expect(qualification_source_contract(
    "src/app/io/_CliCommands/run_commands.spl",
    ["cli_run_file(\"src/app/gen_lean/main.spl\""],
    ["_cli_process_run(\"./bin/simple\", args)"]
)).to_equal("safe")
val (_fix_out, _fix_err, fix_code, _fix_ms) = qualification_run_command(
    ["fix", "test/fixtures/pure_simple_tooling/clean.spl", "--dry-run"], 30000)
expect(fix_code).to_equal(0)
expect(qualification_termination_probe()).to_equal("safe")
```

</details>

#### REQ-003 REQ-007 REQ-009 REQ-010 NFR-004 gates essential tools on the fresh Stage 4 CLI

- REQ-003 REQ-007 REQ-009 REQ-010 NFR-004 gates essential tools on the fresh Stage 4 CLI
- Run the fresh test runner sanity
- Run the fresh lint sanity
- Run the fresh duplicate checker sanity


<details>
<summary>Executable SSpec</summary>

Runnable source: 35 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("REQ-003 REQ-007 REQ-009 REQ-010 NFR-004 gates essential tools on the fresh Stage 4 CLI")
step("Run the fresh test runner sanity")
expect(qualification_source_contract(
    "scripts/check/check-bootstrap-essential-tools-smoke.shs",
    ["error=timeout_command_missing", "run_probe test_runner_pass 0", "run_probe test_runner_fail 1", "run_probe test_runner_indexed_u8_fail 1", "error=test_runner_indexed_u8_failure_summary_missing", "error=test_runner_indexed_u8_assertion_missing", "run_probe test_runner_empty 1", "run_probe test_runner_forged 1", "essential_test_runner_smoke=true"],
    ["src/compiler_rust", "|| true"]
)).to_equal("safe")
step("Run the fresh lint sanity")
expect(qualification_source_contract(
    "scripts/check/check-bootstrap-essential-tools-smoke.shs",
    ["run_probe lint_clean 0", "run_probe lint_deny 1", "run_probe lint_directory 1", "error=lint_directory_write_rule_missing", "error=lint_directory_direct_write_rule_missing", "error=lint_directory_parse_rule_missing", "error=lint_directory_summary_missing", "run_jsonl_probe lint_json_deny 1", "run_jsonl_probe lint_invalid_profile 2", "error=${label}_jsonl_stderr_not_empty", "\"type\":\"lint-diagnostic\"", "error=lint_json_aggregate_summary_wrong", "error=lint_json_non_json_line", "error=lint_json_human_output", "essential_lint_smoke=true"],
    ["SIMPLE_NO_STUB_FALLBACK=0"]
)).to_equal("safe")
step("Run the fresh duplicate checker sanity")
expect(qualification_source_contract(
    "scripts/check/check-bootstrap-essential-tools-smoke.shs",
    ["scripts/check/validate-json.spl", "run_probe validate_json_valid 0", "run_probe validate_json_malformed 1", "run_probe validate_json_trailing 1", "test/fixtures/duplication/clean_pair", "--no-default-excludes", "run_json_probe duplicate_clean 0", "run_json_probe duplicate_token_uncached 1", "run_json_probe duplicate_cosine_uncached 1", "assert_duplicate_found_json duplicate_token_uncached token", "assert_duplicate_found_json duplicate_cosine_uncached cosine", "error=duplicate_token_cache_create_changed", "duplicate_args='duplicates", "duplicates/ignored/**", "\"total_groups\": 1", "\"total_occurrences\": 2", "\"total_lines\": 10", "\"files_affected\": 2", "\"occurrences\": 2", "\"lines_per_block\": 5", "\"file\": \"duplicates/a.spl\"", "\"file\": \"duplicates/b.spl\"", "\"line_start\": 1", "\"line_end\": 5", "error=${{label}}_ignored_c_included", "error=${{label}}_ignored_d_included", "run_probe duplicate_config_invalid_mode 2", "run_json_probe duplicate_config_mode_override 0", "error=duplicate_config_mode_override_ignored", "run_probe duplicate_config_invalid_format 2", "run_json_probe duplicate_config_format_override 0", "error=duplicate_config_format_override_ignored", "essential_duplicate_checker_smoke=true", "bootstrap_essential_tools_smoke=true"],
    ["bin/simple duplicate-check", "src/compiler/90.tools/duplicate_check/main.spl"]
)).to_equal("safe")
expect(qualification_source_contract(
    "scripts/check/validate-json.spl",
    ["json_parse_with_error(file_read(args[0])).1 == \"\"", "if args.len() != 1", "return 2"],
    ["jsonl_content_is_valid"]
)).to_equal("safe")
expect(qualification_source_contract(
    "scripts/bootstrap/bootstrap-from-scratch.sh",
    ["run_logged stage4-essential-tools-smoke run_timeout_kill 180 env", "SIMPLE_BINARY=\"$(absolute_path \"${full_bin}\")\"", "sh scripts/check/check-bootstrap-essential-tools-smoke.shs"],
    []
)).to_equal("safe")
expect(qualification_source_contract(
    "src/app/cli/_CliMain/main_and_help.spl",
    ["run_duplicate_check(filtered_args)"],
    ["cli_run_file(\"src/compiler/90.tools/duplicate_check/main.spl\""]
)).to_equal("safe")
```

</details>

#### REQ-007 REQ-008 REQ-012 REQ-013 NFR-001 NFR-008 NFR-010 NFR-012 rejects unsafe paths and stale fallbacks

- REQ-007 REQ-008 REQ-012 REQ-013 NFR-001 NFR-008 NFR-010 NFR-012 rejects unsafe paths and stale fallbacks
- Reject unsafe paths and stale fallbacks
   - Expected: qualification_hostile_path_probe() equals `safe`
   - Expected: qualification_daemon_cache_probe() equals `safe`


<details>
<summary>Executable SSpec</summary>

Runnable source: 115 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("REQ-007 REQ-008 REQ-012 REQ-013 NFR-001 NFR-008 NFR-010 NFR-012 rejects unsafe paths and stale fallbacks")
step("Reject unsafe paths and stale fallbacks")
expect(qualification_source_contract(
    "src/compiler/90.tools/duplicate_check/detector_files.spl",
    ["rt_path_absolute", "dir_walk_native"],
    ["shell_output"]
)).to_equal("safe")
expect(qualification_source_contract(
    "src/compiler/90.tools/duplicate_check/doc_extractor.spl",
    ["file_read", "collect_files"],
    ["shell_output", "build_exclude_args"]
)).to_equal("safe")
expect(qualification_source_contract(
    "src/compiler/90.tools/duplicate_check/parallel.spl",
    ["cpu_count()"],
    ["shell_output", "nproc"]
)).to_equal("safe")
expect(qualification_source_contract(
    "src/compiler/90.tools/duplicate_check/main.spl",
    ["find_duplicates_with_options", "lexical_runtime_config(config, mode)"],
    ["run_fast_token_gate", "scripts/audit/fast_duplicate_check.spl"]
)).to_equal("safe")
expect(qualification_source_contract(
    "src/compiler/90.tools/duplicate_check/_Detector/similarity_grouping.spl",
    ["progress_tick(config, \"compare pass\", comparison_count, 0, start_ms, last_ms)", "group_occurrence_key", "source.lines()"],
    ["comparison_count, comparison_count, start_ms"]
)).to_equal("safe")
expect(qualification_source_contract(
    "src/compiler/90.tools/duplicate_check/_Detector/interner_and_logging.spl",
    ["val count_text = if total > 0:", r"[dupcheck] {phase}: {count_text} elapsed=", "source.lines()"],
    [r"{done}/{total} ({pct}%) elapsed="]
)).to_equal("safe")
expect(qualification_source_contract(
    "src/compiler_rust/compiler/src/pipeline/native_project/compiler.rs",
    ["persist_compiled_object", "temp.persist(cache_path)", "no_mangle"],
    []
)).to_equal("safe")
expect(qualification_source_contract(
    "src/compiler_rust/compiler/src/pipeline/native_project/mod.rs",
    ["effective_backend", "SIMPLE_BACKEND", "opt_level"],
    []
)).to_equal("safe")
expect(qualification_source_contract(
    "scripts/audit/fast_duplicate_check.spl",
    ["dir_walk_native(config.path)", "files.sort()"],
    ["process_run(\"/bin/sh\"", "fn shell_quote"]
)).to_equal("safe")
expect(qualification_hostile_path_probe()).to_equal("safe")
expect(qualification_source_contract(
    "scripts/setup/setup.shs",
    ["native_hash_is_valid", "mcp_probe_native", "mcp_probe_lsp_native", "_mcp_probe_identity", "_lsp_mcp_probe_identity", "$1.sha256", "mkdir -p \"${log_dir}\"", "SIMPLE_LSP_MCP_NATIVE", "\"id\":\"lsp-call-probe\".*\"result\""],
    ["SKIP_NATIVE_PROBE", "_mcp_probe_stat", "_lsp_mcp_probe_stat", "SIMPLE_MCP_NATIVE_PROBE_QUICK_TIMEOUT", "probe_quick_ok"]
)).to_equal("safe")
expect(qualification_source_contract(
    "scripts/check/check-mcp-native-smoke.shs",
    ["MCP_LOG_BASELINE", "MCP_FIRST_LOG_LINE", "mcp_first.log", "MCP_RC2", "MCP_PROBE_CACHE_HIT", "_selected_native", "_repaired_hash", "probe_tools_call_ok wrapper=simple_mcp_server"],
    ["ls \"${_mcp_probe_cache_dir}\"/*.stamp", "no_stamp_found_skipping_stale_test", "cache_dir_absent_skipping_stale_test"]
)).to_equal("safe")
expect(qualification_source_contract(
    "bin/simple.cmd",
    ["resolve_native_tool.ps1", "%*", "-Kind simple"],
    ["BOOTSTRAP_BIN", "CURRENT_DRIVER_BIN", "compiler_rust"]
)).to_equal("safe")
expect(qualification_source_contract(
    "bin/simple_mcp_server.cmd",
    ["resolve_native_tool.ps1", "%*", "-Kind mcp"],
    ["ALLOW_SOURCE_FALLBACK", ":source", "compiler_rust"]
)).to_equal("safe")
expect(qualification_source_contract(
    "bin/simple_lsp_mcp_server.cmd",
    ["resolve_native_tool.ps1", "%*", "-Kind lsp"],
    [":source", "simple.cmd\" run", "compiler_rust", "PREFER_NATIVE"]
)).to_equal("safe")
expect(qualification_source_contract(
    "bin/resolve_native_tool.ps1",
    ["Get-FileHash", ".sha256", "if ($Kind -ne \"simple\")", "Invoke-BoundedProbe", "simple_pipe", "lsp_symbols", "windows-native-v1"],
    ["ALLOW_SOURCE_FALLBACK", "PREFER_NATIVE"]
)).to_equal("safe")
expect(qualification_source_contract(
    "scripts/check/check-windows-tool-wrapper-contract.ps1",
    ["New-FakeNative", "without a sidecar", "mcp-error", "lsp-error", "content-addressed stamp", "explicit override fell through"],
    []
)).to_equal("safe")
expect(qualification_source_contract(
    "src/app/test_daemon/light_daemon.spl",
    ["cached.result_status != -1"],
    ["cached.test_path != \"\""]
)).to_equal("safe")
expect(qualification_source_contract(
    "src/app/cli/_CliMain/main_and_help.spl",
    ["use app.test_daemon.main.{cli_test_daemon}"],
    ["use app.io.cli_commands.{cli_test_daemon}"]
)).to_equal("safe")
expect(qualification_source_contract(
    "src/app/test_daemon/binary.spl",
    ["env_get(\"SIMPLE_BINARY\")", "cli_get_args()", "file_exists(configured)"],
    []
)).to_equal("safe")
expect(qualification_source_contract(
    "src/app/test_daemon/client.spl",
    ["process_spawn_async(test_daemon_simple_binary(), [\"test-daemon\", \"start\"])"],
    ["process_spawn_async(\"/bin/sh\"", "bin/simple test-daemon start"]
)).to_equal("safe")
expect(qualification_source_contract(
    "src/app/io/_CliCommands/handler_commands.spl",
    [],
    ["test-daemon run is unavailable", "fn cli_test_daemon("]
)).to_equal("safe")
expect(qualification_source_contract(
    "test/05_perf/duplicate_check_benchmark_spec.spl",
    ["run_benchmark"],
    ["expect(true)." + "to_equal(true)"]
)).to_equal("safe")
expect(qualification_daemon_cache_probe()).to_equal("safe")
```

</details>

#### REQ-015 and NFR-005 through NFR-009 retain measurable qualification evidence

- REQ-015 and NFR-005 through NFR-009 retain measurable qualification evidence
- Measure warm tooling budgets


<details>
<summary>Executable SSpec</summary>

Runnable source: 22 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("REQ-015 and NFR-005 through NFR-009 retain measurable qualification evidence")
step("Measure warm tooling budgets")
expect(qualification_measure_warm(["check", "test/fixtures/pure_simple_tooling/clean.spl"])).to_be_less_than(2000)
expect(qualification_measure_warm(["lint", "test/fixtures/pure_simple_tooling/clean.spl"])).to_be_less_than(2000)
expect(qualification_measure_warm(["fmt", "test/fixtures/pure_simple_tooling/clean.spl", "--check"])).to_be_less_than(2000)
expect(qualification_measure_warm(["test", "--no-session-daemon", "--assert-ran", "test/fixtures/pure_simple_tooling/sibling_describe_green_spec.spl"])).to_be_less_than(3000)
expect(qualification_source_contract(
    "scripts/check/check-test-runner-rss-batch.shs",
    ["TEST_RUNNER_RSS_FILE_COUNT:-500", "--batch-size=", "Batch worker: pid=", "parent_max_rss_kib", "expected_examples=$(( FILE_COUNT * 2 ))"],
    ["expect(true)." + "to_equal(true)"]
)).to_equal("safe")
expect(qualification_source_contract(
    "scripts/check/check-mcp-lsp-nfr-evidence.shs",
    ["MCP_LSP_NFR_SAMPLES:-20", "REQUEST_P95_MAX_MS", "RSS_MAX_KIB", "native_sha256_sidecar"],
    ["src/app/mcp/main.spl --mode", "src/app/simple_lsp_mcp/main.spl --mode"]
)).to_equal("safe")
expect(qualification_source_contract(
    "doc/06_spec/03_system/app/tooling/feature/pure_simple_tool_infra_hardening_spec.md",
    ["Admit a pure-Simple production runtime", "Measure warm tooling budgets"],
    []
)).to_equal("safe")
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 5 |
| Active scenarios | 5 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


## Related Documentation

- **Requirements:** `REQ-001 through REQ-015`
- **Plan:** `doc/03_plan/sys_test/pure_simple_tool_infra_hardening.md`
- **Design:** `doc/05_design/pure_simple_tool_infra_hardening.md`
- **Research:** `doc/01_research/local/pure_simple_tool_infra_hardening.md`


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-SYSTEM`
- `REQ-001`
- `REQ-015`
- `REQ-002`
- `REQ-011`
- `REQ-006`
- `REQ-009`
- `REQ-010`
- `REQ-014`
- `REQ-007`
- `REQ-008`
- `REQ-012`
- `REQ-013`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `51a64d0a9fa012afadb755c9df897aa9804b82fe639e69c90f7da2fea98b8ec6`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `51a64d0a9fa012afadb755c9df897aa9804b82fe639e69c90f7da2fea98b8ec6`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `51a64d0a9fa012afadb755c9df897aa9804b82fe639e69c90f7da2fea98b8ec6`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **86/100**; effective score: **86/100**; blockers: **0**.

SSpec documentization score: 86/100
source: test/03_system/app/tooling/feature/pure_simple_tool_infra_hardening_spec.spl
mirror: doc/06_spec/03_system/app/tooling/feature/pure_simple_tool_infra_hardening_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/03_system/app/tooling/feature/pure_simple_tool_infra_hardening_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/app/tooling/feature/pure_simple_tool_infra_hardening_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/app/tooling/feature/pure_simple_tool_infra_hardening_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 3 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/03_system/app/tooling/feature/pure_simple_tool_infra_hardening_spec.spl:157:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'REQ-001 REQ-002 REQ-011 NFR-003 NFR-011 NFR-012 admits only a truthful production runtime and inventory' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/app/tooling/feature/pure_simple_tool_infra_hardening_spec.spl:362:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'REQ-003 REQ-007 REQ-009 REQ-010 NFR-004 gates essential tools on the fresh Stage 4 CLI' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/app/tooling/feature/pure_simple_tool_infra_hardening_spec.spl:399:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'REQ-007 REQ-008 REQ-012 REQ-013 NFR-001 NFR-008 NFR-010 NFR-012 rejects unsafe paths and stale fallbacks' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
