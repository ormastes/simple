# stage4_smoke_gate_spec

> Purpose: Prove that bootstrap stage4 smoke gate.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 18 | 18 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# stage4_smoke_gate_spec

Purpose: Prove that bootstrap stage4 smoke gate.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler/bootstrap/stage4_smoke_gate_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Purpose and audience
Purpose: Prove that bootstrap stage4 smoke gate.
Audience: compiler and tooling engineers who maintain this spec.

## Scenarios

### bootstrap stage4 smoke gate

#### keeps diagnostic whole-archive mode out of canonical bootstrap

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- keeps diagnostic whole-archive mode out of canonical bootstrap
- Verify: keeps diagnostic whole-archive mode out of canonical bootstrap


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("keeps diagnostic whole-archive mode out of canonical bootstrap")
step("Verify: keeps diagnostic whole-archive mode out of canonical bootstrap")
# @req: REQ-COMPILER-BOOTSTRAP-001
val script = rt_file_read_text("scripts/bootstrap/bootstrap-from-scratch.sh") ?? ""

expect(script).to_not_contain("SIMPLE_NATIVE_FORCE_WHOLE_ARCHIVE=1")
```

</details>

#### fails bootstrap when the freshly built full CLI cannot execute code

- fails bootstrap when the freshly built full CLI cannot execute code
- Verify: fails bootstrap when the freshly built full CLI cannot execute code


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("fails bootstrap when the freshly built full CLI cannot execute code")
step("Verify: fails bootstrap when the freshly built full CLI cannot execute code")
val script = rt_file_read_text("scripts/bootstrap/bootstrap-from-scratch.sh") ?? ""

expect(script).to_contain("stage4_smoke")
expect(script).to_contain("run_timeout 30")
expect(script).to_contain("-c 'print(1+1)'")
expect(script).to_contain("error: stage4 binary failed smoke test")
```

</details>

#### gates test lint and duplicate-check on the fresh Stage 4 CLI

- gates test lint and duplicate-check on the fresh Stage 4 CLI
- Verify: gates test lint and duplicate-check on the fresh Stage 4 CLI
   - Expected: smoke.split("run_with_timeout env SIMPLE_BOOTSTRAP= SIMPLE_RUNTIME_PATH= SIMPLE_LIB=").len() equals `3`
   - Expected: workflow.split("'scripts/check/check-bootstrap-essential-tools-smoke.shs'").len() equals `3`
   - Expected: workflow.split("'scripts/check/validate-json.spl'").len() equals `3`
   - Expected: workflow.split("'scripts/check/validate-jsonl.spl'").len() equals `3`
   - Expected: workflow.split("'test/01_unit/lib/core/list_constructor_hardening_spec.spl'").len() equals `3`
   - Expected: workflow.split("'src/app/io/cli_fix_options.spl'").len() equals `3`
   - Expected: workflow.split("'src/app/io/cli_fmt_options.spl'").len() equals `3`
   - Expected: workflow.split("'src/app/io/cli_lint_commands.spl'").len() equals `3`
   - Expected: workflow.split("'src/app/io/_CliCompile/**'").len() equals `3`
   - Expected: workflow.split("'test/01_unit/app/cli/bootstrap_main_source_spec.spl'").len() equals `3`
   - Expected: workflow.split("'test/01_unit/app/compile/cli_compile_surface_spec.spl'").len() equals `3`
   - Expected: workflow.split("'test/02_integration/os/port/runtime_bundle_policy_spec.spl'").len() equals `3`
   - Expected: workflow.split("'test/03_system/app/lint_cli_contract_spec.spl'").len() equals `3`


<details>
<summary>Executable SSpec</summary>

Runnable source: 84 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("gates test lint and duplicate-check on the fresh Stage 4 CLI")
step("Verify: gates test lint and duplicate-check on the fresh Stage 4 CLI")
val bootstrap = rt_file_read_text("scripts/bootstrap/bootstrap-from-scratch.sh") ?? ""
val smoke = rt_file_read_text("scripts/check/check-bootstrap-essential-tools-smoke.shs") ?? ""
val cli = rt_file_read_text("src/app/cli/_CliMain/main_and_help.spl") ?? ""
val workflow = rt_file_read_text(".github/workflows/rust-bootstrap-multiplatform.yml") ?? ""

expect(bootstrap).to_contain("run_logged stage4-essential-tools-smoke run_timeout_kill 180 env")
expect(bootstrap).to_contain("SIMPLE_BINARY=\"$(absolute_path \"${{full_bin}}\")\"")
expect(smoke).to_contain("SIMPLE_NO_STUB_FALLBACK=1")
expect(smoke).to_contain("SIMPLE_FRONTEND_DELEGATED=1")
expect(smoke).to_contain("SIMPLE_BOOTSTRAP= SIMPLE_RUST_SEED_WARNING=")
expect(smoke.split("run_with_timeout env SIMPLE_BOOTSTRAP= SIMPLE_RUNTIME_PATH= SIMPLE_LIB=").len()).to_equal(3)
expect(smoke).to_contain("error=rust_seed_binary")
expect(smoke).to_contain("essential_tools_pure_simple_identity=true")
expect(smoke).to_contain("timeout -k 5s 30s")
expect(smoke).to_contain("run_probe test_runner_pass 0")
expect(smoke).to_contain("run_probe list_constructor 0")
expect(smoke).to_contain("essential_list_constructor_smoke=true")
expect(smoke).to_contain("run_probe test_runner_fail 1")
expect(smoke).to_contain("run_probe test_runner_indexed_u8_fail 1")
expect(smoke).to_contain("error=test_runner_indexed_u8_failure_summary_missing")
expect(smoke).to_contain("error=test_runner_indexed_u8_assertion_missing")
expect(smoke).to_contain("run_probe test_runner_empty 1")
expect(smoke).to_contain("run_probe lint_clean 0")
expect(smoke).to_contain("run_probe lint_deny 1")
expect(smoke).to_contain("run_probe lint_directory 1")
expect(smoke).to_contain("error=lint_directory_direct_write_rule_missing")
expect(smoke).to_contain("error=lint_directory_parse_rule_missing")
expect(smoke).to_contain("run_jsonl_probe lint_json_deny 1")
expect(smoke).to_contain("run_jsonl_probe lint_invalid_profile 2")
expect(smoke).to_contain("error=${{label}}_jsonl_stderr_not_empty")
expect(smoke).to_contain("error=lint_json_aggregate_summary_wrong")
expect(smoke).to_contain("validate-jsonl.spl")
expect(smoke).to_contain("error=${{label}}_invalid_jsonl")
expect(smoke).to_contain("error=lint_json_non_json_line")
expect(smoke).to_contain("error=lint_json_human_output")
expect(smoke).to_contain("scripts/check/validate-json.spl")
expect(smoke).to_contain("run_probe validate_json_valid 0")
expect(smoke).to_contain("run_probe validate_json_malformed 1")
expect(smoke).to_contain("run_probe validate_json_trailing 1")
expect(smoke).to_contain("run_json_probe duplicate_clean 0")
expect(smoke).to_contain("run_json_probe duplicate_token_uncached 1")
expect(smoke).to_contain("run_json_probe duplicate_cosine_uncached 1")
expect(smoke).to_contain("assert_duplicate_found_json duplicate_token_uncached token")
expect(smoke).to_contain("assert_duplicate_found_json duplicate_cosine_uncached cosine")
expect(smoke).to_contain("error=duplicate_token_cache_create_changed")
expect(smoke).to_contain("run_json_probe duplicate_config_mode_override 0")
expect(smoke).to_contain("run_json_probe duplicate_config_format_override 0")
expect(smoke).to_contain("duplicate_args='duplicates")
expect(smoke).to_contain("duplicates/ignored/**")
expect(smoke).to_contain("\"total_groups\": 1")
expect(smoke).to_contain("\"total_occurrences\": 2")
expect(smoke).to_contain("\"total_lines\": 10")
expect(smoke).to_contain("\"files_affected\": 2")
expect(smoke).to_contain("\"occurrences\": 2")
expect(smoke).to_contain("\"lines_per_block\": 5")
expect(smoke).to_contain("\"file\": \"duplicates/a.spl\"")
expect(smoke).to_contain("\"file\": \"duplicates/b.spl\"")
expect(smoke).to_contain("\"line_start\": 1")
expect(smoke).to_contain("\"line_end\": 5")
expect(smoke).to_contain("error=${{label}}_ignored_c_included")
expect(smoke).to_contain("error=${{label}}_ignored_d_included")
expect(smoke).to_contain("bootstrap_essential_tools_smoke=true")
expect(smoke).to_contain("usage: $0 [stage4-binary]")
expect(smoke).to_contain("error=conflicting_simple_binary_argument")
expect(smoke).to_contain("SIMPLE_BINARY=$1")
expect(smoke).to_not_contain("src/compiler_rust")
expect(smoke).to_not_contain("bin/simple duplicate-check")
expect(cli).to_contain("return run_duplicate_check(filtered_args)")
expect(cli).to_not_contain("cli_run_file(\"src/compiler/90.tools/duplicate_check/main.spl\"")
expect(workflow.split("'scripts/check/check-bootstrap-essential-tools-smoke.shs'").len()).to_equal(3)
expect(workflow.split("'scripts/check/validate-json.spl'").len()).to_equal(3)
expect(workflow.split("'scripts/check/validate-jsonl.spl'").len()).to_equal(3)
expect(workflow.split("'test/01_unit/lib/core/list_constructor_hardening_spec.spl'").len()).to_equal(3)
expect(workflow.split("'src/app/io/cli_fix_options.spl'").len()).to_equal(3)
expect(workflow.split("'src/app/io/cli_fmt_options.spl'").len()).to_equal(3)
expect(workflow.split("'src/app/io/cli_lint_commands.spl'").len()).to_equal(3)
expect(workflow.split("'src/app/io/_CliCompile/**'").len()).to_equal(3)
expect(workflow.split("'test/01_unit/app/cli/bootstrap_main_source_spec.spl'").len()).to_equal(3)
expect(workflow.split("'test/01_unit/app/compile/cli_compile_surface_spec.spl'").len()).to_equal(3)
expect(workflow.split("'test/02_integration/os/port/runtime_bundle_policy_spec.spl'").len()).to_equal(3)
expect(workflow.split("'test/03_system/app/lint_cli_contract_spec.spl'").len()).to_equal(3)
```

</details>

#### runs every maintained test surface for release bootstrap

- runs every maintained test surface for release bootstrap
- Verify: runs every maintained test surface for release bootstrap


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("runs every maintained test surface for release bootstrap")
step("Verify: runs every maintained test surface for release bootstrap")
val script = rt_file_read_text("scripts/bootstrap/bootstrap-from-scratch.sh") ?? ""

expect(script).to_contain("--release          Deploy, then run the release-blocking whole test suite")
expect(script).to_contain("run_logged stage6-whole-tests \"${{deployed_bin}}\" test test --whole --mode=interpreter")
```

</details>

#### rejects seed fallback and gates the full candidate before deployment

- rejects seed fallback and gates the full candidate before deployment
- Verify: rejects seed fallback and gates the full candidate before deployment


<details>
<summary>Executable SSpec</summary>

Runnable source: 47 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("rejects seed fallback and gates the full candidate before deployment")
step("Verify: rejects seed fallback and gates the full candidate before deployment")
val script = rt_file_read_text("scripts/bootstrap/bootstrap-from-scratch.sh") ?? ""
val admission = rt_file_read_text("scripts/check/cert/redeploy_gate/candidate_frontend_admission.shs") ?? ""
val check_entry = rt_file_read_text("src/app/cli/check_entry.spl") ?? ""

expect(script).to_contain("refusing seed fallback")
expect(script).to_contain("CANDIDATE_FRONTEND_ROOT=${{repo_root}}")
expect(script).to_contain(". \"${{repo_root}}/scripts/check/cert/redeploy_gate/candidate_frontend_admission.shs\"")
expect(script).to_contain("if ! simple_binary_is_valid \"${{full_bin}}\"; then")
expect(admission).to_contain("candidate_frontend_smoke() (")
expect(admission).to_contain("candidate_frontend_delegate_fidelity() (")
expect(admission).to_contain("SIMPLE_FRONTEND_DELEGATE=\"$delegate\"")
expect(admission).to_contain("SIMPLE_FRONTEND_DELEGATED=0")
expect(admission).to_contain("delegate.cmd")
expect(admission).to_contain("@exit /b 17")
expect(admission).to_contain("check ignored.spl")
expect(admission).to_contain("[ \"$probe_status\" -eq 17 ]")
expect(admission).to_contain("stage4-delegate-stdout")
expect(admission).to_contain("stage4-delegate-stderr")
expect(admission).to_contain("candidate_frontend_delegate_fidelity \"$candidate\" || return 1")
expect(admission).to_contain("grep -Fq 'stage4-delegate-stdout'")
expect(admission).to_contain("grep -Fq 'stage4-delegate-stderr'")
expect(admission).to_contain("env_probe=$(SIMPLE_BINARY=\"$candidate\"")
expect(admission).to_contain("SIMPLE_FRONTEND_DELEGATE=\"$candidate\"")
expect(admission).to_contain("[ \"$env_probe\" = true ] || return 1")
expect(admission).to_contain("fixtures/p2_add.spl")
expect(admission).to_contain("--runtime-bundle core-c-bootstrap")
expect(admission).to_contain("--mode one-binary")
expect(admission).to_contain("cat \"$probe_dir/build.log\" >&2")
expect(admission).to_contain("--mode definitely-invalid-mode")
expect(admission).to_contain("trap 'rm -rf \"$probe_dir\"' 0")
expect(admission).to_contain("simple_binary_is_valid() (")
expect(admission).to_contain("version=$(SIMPLE_BINARY=\"$candidate\"")
expect(admission).to_contain("__SIMPLE_CANDIDATE_ENV_ABI__")
val configured_pos: i64 = check_entry.find("val configured = env_get(\"SIMPLE_BINARY\")")
val configured_bin_pos: i64 = check_entry.find("val configured_bin = env_get(\"SIMPLE_BIN\")")
val uname_pos: i64 = check_entry.find("process_run_timeout(\"uname\"")
expect(check_entry).to_contain("use app.io.env_ops.{{env_get}}")
expect(check_entry).to_contain("configured != nil and configured != \"\" and file_exists(configured)")
expect(check_entry).to_contain("configured_bin != nil and configured_bin != \"\" and file_exists(configured_bin)")
expect(configured_pos).to_be_greater_than(-1)
expect(configured_bin_pos).to_be_greater_than(configured_pos)
expect(uname_pos).to_be_greater_than(configured_bin_pos)
expect(script).to_contain("stage4-redeploy-gate")
expect(script).to_contain("redeploy_gate/redeploy_gate.shs")
```

</details>

#### builds and requires the dedicated compiler backfill for a full CLI

- builds and requires the dedicated compiler backfill for a full CLI
- Verify: builds and requires the dedicated compiler backfill for a full CLI


<details>
<summary>Executable SSpec</summary>

Runnable source: 20 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("builds and requires the dedicated compiler backfill for a full CLI")
step("Verify: builds and requires the dedicated compiler backfill for a full CLI")
val script = rt_file_read_text("scripts/bootstrap/bootstrap-from-scratch.sh") ?? ""
val workflow = rt_file_read_text(".github/workflows/rust-bootstrap-multiplatform.yml") ?? ""
val full_cli_implication: i64 = script.find("if [ \"${{deploy}}\" -eq 1 ] || [ \"${{bootstrap_mode}}\" = \"one-binary\" ]; then")
val reuse_gate: i64 = script.find("if [ \"${{full_bootstrap}}\" -eq 0 ]; then")
val workflow_backfill: i64 = workflow.find("cargo build --profile bootstrap -p simple-compiler-backfill")
val workflow_full_cli: i64 = workflow.find("mcp_flag=--full-cli")

expect(script).to_contain("compiler_backfill_lib=\"src/compiler_rust/target/bootstrap/${{archive_prefix}}simple_compiler_backfill${{archive_suffix}}\"")
expect(script).to_contain("-p simple-compiler-backfill")
expect(script).to_contain("full CLI bootstrap needs the compiler backfill archive")
expect(script).to_contain("full CLI bootstrap refuses a stale compiler backfill")
expect(script).to_contain("rust_rebuilt=1")
expect(script).to_contain("[ \"${{rust_rebuilt}}\" -eq 1 ]")
expect(script).to_contain("supported on native Linux and macOS hosts")
expect(full_cli_implication).to_be_less_than(reuse_gate)
expect(workflow_backfill).to_be_greater_than(-1)
expect(workflow_backfill).to_be_less_than(workflow_full_cli)
```

</details>

#### publishes the Linux LLVM full CLI with its hosted providers

- publishes the Linux LLVM full CLI with its hosted providers
- Verify: publishes the Linux LLVM full CLI with its hosted providers


<details>
<summary>Executable SSpec</summary>

Runnable source: 40 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("publishes the Linux LLVM full CLI with its hosted providers")
step("Verify: publishes the Linux LLVM full CLI with its hosted providers")
val workflow = rt_file_read_text(".github/workflows/rust-bootstrap-multiplatform.yml") ?? ""
val full_build_pos: i64 = workflow.find("Build and sanity-check pure-Simple stages")
val failure_upload_pos: i64 = workflow.find("Upload pure-Simple bootstrap failure logs")
val stage_pos: i64 = workflow.find("Stage hosted full-CLI providers")
val upload_pos: i64 = workflow.find("Upload hosted full CLI")
val parity_pos: i64 = workflow.find("Run Rust-seed custom enum identity parity")
val full_build_block = workflow.substring(full_build_pos, failure_upload_pos)
val failure_upload_block = workflow.substring(failure_upload_pos, stage_pos)
val upload_block = workflow.substring(upload_pos, parity_pos)

expect(full_build_pos).to_be_greater_than(-1)
expect(failure_upload_pos).to_be_greater_than(full_build_pos)
expect(stage_pos).to_be_greater_than(failure_upload_pos)
expect(upload_pos).to_be_greater_than(stage_pos)
expect(parity_pos).to_be_greater_than(upload_pos)
expect(full_build_block).to_contain("id: pure_simple_bootstrap")
expect(full_build_block).to_contain("scripts/bootstrap/bootstrap-from-scratch.sh")
expect(full_build_block).to_contain("--full-bootstrap")
expect(failure_upload_block).to_contain("if: failure() && steps.pure_simple_bootstrap.outcome == 'failure' && runner.os == 'Linux'")
expect(failure_upload_block).to_not_contain("matrix.backend == 'llvm'")
expect(failure_upload_block).to_contain("uses: actions/upload-artifact@v4")
expect(failure_upload_block).to_contain("name: bootstrap-failure-logs-${{ matrix.backend }}-${{ github.sha }}")
expect(failure_upload_block).to_contain("path: build/bootstrap/logs/**")
expect(failure_upload_block).to_contain("if-no-files-found: error")
expect(failure_upload_block).to_contain("retention-days: 7")
expect(workflow).to_contain("if: runner.os == 'Linux' && matrix.backend == 'llvm'")
expect(workflow).to_contain("cargo build --manifest-path src/compiler_rust/Cargo.toml --profile bootstrap -p simple-runtime")
expect(workflow).to_contain("cargo build --manifest-path src/compiler_rust/Cargo.toml --profile bootstrap -p spl_fonts")
expect(workflow).to_contain("cargo build --manifest-path src/runtime/spl_winit/Cargo.toml --release")
expect(upload_block).to_contain("uses: actions/upload-artifact@v4")
expect(upload_block).to_contain("build/bootstrap/full/**/simple")
expect(upload_block).to_contain("build/bootstrap/lib/libspl_fonts.so")
expect(upload_block).to_contain("src/compiler_rust/target/bootstrap/deps/libsimple_runtime.so")
expect(upload_block).to_contain("src/runtime/spl_winit/target/release/libspl_winit.so")
expect(upload_block).to_contain("if-no-files-found: error")
expect(upload_block).to_not_contain("src/compiler_rust/target/bootstrap/simple")
expect(upload_block).to_not_contain("simple_seed")
```

</details>

#### uses Cargo staticlib names for both Windows toolchains

- uses Cargo staticlib names for both Windows toolchains
- Verify: uses Cargo staticlib names for both Windows toolchains


<details>
<summary>Executable SSpec</summary>

Runnable source: 21 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("uses Cargo staticlib names for both Windows toolchains")
step("Verify: uses Cargo staticlib names for both Windows toolchains")
val script = rt_file_read_text("scripts/bootstrap/bootstrap-from-scratch.sh") ?? ""
val platform_pos: i64 = script.find("if [ \"${{os}}\" = \"windows\" ]; then")
val hash_pos: i64 = script.find("hash_file() {")
val policy = script.substring(platform_pos, hash_pos)
val msvc_pos: i64 = policy.find("if [ \"${{SIMPLE_LINKER_FLAVOR:-}}\" = \"msvc\" ]; then")
val gnu_pos: i64 = policy.find("elif [ \"${{SIMPLE_LINKER_FLAVOR:-}}\" = \"gnu\" ]; then")
val platform_gnu_pos: i64 = policy.find("elif [ \"${{PLATFORM_ABI}}\" = \"gnu\" ]; then")
expect(platform_pos).to_be_greater_than(-1)
expect(hash_pos).to_be_greater_than(platform_pos)
expect(msvc_pos).to_be_greater_than(-1)
expect(gnu_pos).to_be_greater_than(msvc_pos)
expect(platform_gnu_pos).to_be_greater_than(gnu_pos)
expect(policy).to_contain("if [ \"${{SIMPLE_LINKER_FLAVOR:-}}\" = \"msvc\" ]; then\n    archive_prefix=\"\"\n    archive_suffix=\".lib\"\n  elif")
expect(policy).to_contain("elif [ \"${{SIMPLE_LINKER_FLAVOR:-}}\" = \"gnu\" ]; then\n    archive_prefix=\"lib\"\n    archive_suffix=\".a\"\n  elif")
expect(policy).to_contain("elif [ \"${{PLATFORM_ABI}}\" = \"gnu\" ]; then\n    archive_prefix=\"lib\"\n    archive_suffix=\".a\"\n  else")
expect(policy).to_contain("else\n    archive_prefix=\"\"\n    archive_suffix=\".lib\"\n  fi\nfi")
expect(script).to_contain("native_all_lib=\"src/compiler_rust/target/bootstrap/${{archive_prefix}}simple_native_all${{archive_suffix}}\"")
expect(script).to_contain("compiler_backfill_lib=\"src/compiler_rust/target/bootstrap/${{archive_prefix}}simple_compiler_backfill${{archive_suffix}}\"")
```

</details>

#### exports the Stage4 pure driver inputs and requests core C

- exports the Stage4 pure driver inputs and requests core C
- Verify: exports the Stage4 pure driver inputs and requests core C


<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("exports the Stage4 pure driver inputs and requests core C")
step("Verify: exports the Stage4 pure driver inputs and requests core C")
val script = rt_file_read_text("scripts/bootstrap/bootstrap-from-scratch.sh") ?? ""
expect(script).to_contain("SIMPLE_RUNTIME_PATH=\"$(pwd)/src/compiler_rust/target/bootstrap\"")

expect(script).to_contain("SIMPLE_BOOTSTRAP_STAGE4=1")
expect(script).to_contain("SIMPLE_COMPILER_PHASE_PROFILE=\"${{SIMPLE_COMPILER_PHASE_PROFILE:-1}}\"")
expect(script).to_contain("SIMPLE_NATIVE_BUILD_TARGET=\"${{PLATFORM}}\"")
expect(script).to_contain("SIMPLE_NATIVE_BUILD_THREADS=\"${{selfhost_jobs}}\"")
expect(script).to_contain("SIMPLE_NATIVE_BUILD_CACHE_DIR=\"${{native_cache_dir}}\"")
expect(script).to_contain("SIMPLE_RUNTIME_PATH=")
expect(script).to_contain("--runtime-bundle core-c-bootstrap")
expect(script).to_contain("--low-memory")
expect(script).to_contain("--mode one-binary")
expect(script).to_contain("--runtime-path \"$(pwd)/src/compiler_rust/target/bootstrap\"")
```

</details>

#### uses supported runtime bundles for Stage 2 and Stage 3

- uses supported runtime bundles for Stage 2 and Stage 3
- Verify: uses supported runtime bundles for Stage 2 and Stage 3


<details>
<summary>Executable SSpec</summary>

Runnable source: 26 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("uses supported runtime bundles for Stage 2 and Stage 3")
step("Verify: uses supported runtime bundles for Stage 2 and Stage 3")
val script = rt_file_read_text("scripts/bootstrap/bootstrap-from-scratch.sh") ?? ""
val stage2_pos: i64 = script.find("# Stage 2: seed compiles bootstrap_main.spl")
val stage3_pos: i64 = script.find("# Stage 3: stage2 recompiles bootstrap_main.spl")
val capability_pos: i64 = script.find("stage2_capability_ok=0")
val stage2_block = script.substring(stage2_pos, stage3_pos)
val stage3_block = script.substring(stage3_pos, capability_pos)

expect(stage2_pos).to_be_greater_than(-1)
expect(stage3_pos).to_be_greater_than(stage2_pos)
expect(capability_pos).to_be_greater_than(stage3_pos)
expect(stage2_block).to_contain("--runtime-bundle core-c-bootstrap")
expect(stage3_block).to_contain("--runtime-bundle core-c-bootstrap")
expect(stage2_block).to_contain("SIMPLE_NATIVE_BUILD_RUST=1")
expect(stage3_block).to_not_contain("SIMPLE_NATIVE_BUILD_RUST=1")
expect(stage3_block).to_contain("SIMPLE_NATIVE_BUILD_TARGET=\"${{PLATFORM}}\"")
expect(stage3_block).to_contain("SIMPLE_NATIVE_BUILD_THREADS=\"${{selfhost_jobs}}\"")
expect(stage3_block).to_contain("SIMPLE_NATIVE_BUILD_CACHE_DIR=\"${{stage3_cache_absolute}}\"")
expect(stage3_block).to_contain("SIMPLE_RUNTIME_PATH=\"${{stage_runtime_absolute}}\"")
expect(stage3_block).to_contain("SIMPLE_NATIVE_RUNTIME_BUNDLE=core-c-bootstrap")
expect(stage3_block).to_contain("-o \"${{stage3_bin}}\" \\\n    src/app/cli/bootstrap_main.spl")
expect(stage3_block).to_not_contain("--entry src/app/cli/bootstrap_main.spl")
expect(stage3_block).to_not_contain("--source src/compiler --source src/app --source src/lib")
expect(script).to_not_contain("--runtime-bundle rust-hosted")
```

</details>

#### resolves a src entry closure before the implicit whole-tree load

- resolves a src entry closure before the implicit whole-tree load
- Verify: resolves a src entry closure before the implicit whole-tree load


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("resolves a src entry closure before the implicit whole-tree load")
step("Verify: resolves a src entry closure before the implicit whole-tree load")
val driver = rt_file_read_text("src/compiler/80.driver/driver.spl") ?? ""
val compile_targets = rt_file_read_text("src/app/io/_CliCompile/compile_targets.spl") ?? ""

expect(driver).to_contain("if nb_entry_env != \"\" and not nb_entry_closure_pre and self.ctx.options.mode == CompileMode.Aot:")
expect(driver).to_not_contain("nb_entry_env != \"\" and not has_project_source and not nb_entry_closure_pre")
expect(compile_targets).to_contain("var discovered: Dict<text, bool> = {}")
expect(compile_targets).to_contain("var resolve_cache: Dict<text, text> = {}")
expect(compile_targets).to_contain("_driver_entry_import_module_paths(content)")
expect(compile_targets).to_contain("resolve_cache[seg_key] = rp")
expect(compile_targets).to_not_contain("hashset_with_capacity")
expect(compile_targets).to_not_contain("hashmap_with_capacity")
```

</details>

#### keeps bootstrap MIR symbol names compatible with the pure frontend

- keeps bootstrap MIR symbol names compatible with the pure frontend
- Verify: keeps bootstrap MIR symbol names compatible with the pure frontend


<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("keeps bootstrap MIR symbol names compatible with the pure frontend")
step("Verify: keeps bootstrap MIR symbol names compatible with the pure frontend")
val globals = rt_file_read_text("src/compiler/50.mir/_MirLowering/bootstrap_globals.spl") ?? ""
val lowering = rt_file_read_text("src/compiler/50.mir/_MirLowering/function_lowering.spl") ?? ""
val module_lowering = rt_file_read_text("src/compiler/50.mir/_MirLowering/module_lowering.spl") ?? ""

expect(globals).to_contain("fn bootstrap_hir_function_symbol_name(module: HirModule, hir_fn: HirFunction) -> text:")
expect(globals).to_contain("val display_name = module.symbols.symbol_display_name(hir_fn.symbol, hir_fn.name)")
expect(globals).to_not_contain("function: HirFunction")
expect(globals).to_not_contain("symbol_display_name(function.symbol, function.name).replace")
expect(lowering).to_contain("val display_name = self.symbols.symbol_display_name(fn_.symbol, fn_.name)")
expect(lowering).to_contain("mir_fn_name = display_name.replace(\"::\", \".\")")
expect(module_lowering).to_contain("for hir_fn in module.functions.values():")
expect(module_lowering).to_contain("function_names.push(hir_fn.name)")
expect(module_lowering).to_not_contain("for function in module.functions.values():")
```

</details>

#### parses comma-separated class mixins in the Stage4 frontend

- parses comma-separated class mixins in the Stage4 frontend
- Verify: parses comma-separated class mixins in the Stage4 frontend


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("parses comma-separated class mixins in the Stage4 frontend")
step("Verify: parses comma-separated class mixins in the Stage4 frontend")
val parser = rt_file_read_text("src/compiler/10.frontend/core/_ParserDecls/fn_struct_decls.spl") ?? ""
val async_tcp = rt_file_read_text("src/lib/nogc_async_mut/io/tcp.spl") ?? ""

expect(parser).to_contain("while par_kind_get() == 160:")
expect(parser).to_contain("parser_advance()\n                parser_expect(6)")
expect(async_tcp).to_contain("class AsyncTcpStream with AsyncRead, AsyncWrite, AsyncClose:")
```

</details>

#### consumes optional suffixes after generic types

- consumes optional suffixes after generic types
- Verify: consumes optional suffixes after generic types


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("consumes optional suffixes after generic types")
step("Verify: consumes optional suffixes after generic types")
val parser = rt_file_read_text("src/compiler/10.frontend/core/parser.spl") ?? ""
val sdn_value = rt_file_read_text("src/lib/common/sdn/value.spl") ?? ""

expect(parser).to_contain("return parser_absorb_optional_suffix(dict_tag)")
expect(parser).to_contain("return parser_absorb_optional_suffix(result_tag)")
expect(parser).to_contain("return parser_absorb_optional_suffix(TYPE_NAMED_BASE + gid)")
expect(sdn_value).to_contain("fn as_dict(self) -> Dict<text, SdnValue>?:")
```

</details>

#### parses fat-arrow match arms with indented statement blocks

- parses fat-arrow match arms with indented statement blocks
- Verify: parses fat-arrow match arms with indented statement blocks


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("parses fat-arrow match arms with indented statement blocks")
step("Verify: parses fat-arrow match arms with indented statement blocks")
val parser = rt_file_read_text("src/compiler/10.frontend/core/parser_stmts.spl") ?? ""
val html_widgets = rt_file_read_text("src/app/ui.render/html_widgets.spl") ?? ""

expect(parser).to_contain("if par_kind_get() == TOK_FAT_ARROW:")
expect(parser).to_contain("if par_kind_get() == TOK_NEWLINE:\n                    arm_body = parse_block()")
expect(html_widgets).to_contain("\"vbox\" =>\n            return render_html_vbox")
```

</details>

#### initializes the Engine2D offscreen optional before backend selection

- initializes the Engine2D offscreen optional before backend selection
- Verify: initializes the Engine2D offscreen optional before backend selection


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("initializes the Engine2D offscreen optional before backend selection")
step("Verify: initializes the Engine2D offscreen optional before backend selection")
val draw_ir = rt_file_read_text("src/lib/gc_async_mut/gpu/engine2d/draw_ir_adv.spl") ?? ""

expect(draw_ir).to_contain("var pending_offscreen: Engine2D? = nil")
expect(draw_ir).to_contain("pending_offscreen = Some(created)")
expect(draw_ir).to_contain("var offscreen = pending_offscreen ?? return")
expect(draw_ir).to_not_contain("var offscreen: Engine2D\n")
```

</details>

#### preserves public visibility on trait declarations

- preserves public visibility on trait declarations
- Verify: preserves public visibility on trait declarations


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("preserves public visibility on trait declarations")
step("Verify: preserves public visibility on trait declarations")
val parser = rt_file_read_text("src/compiler/10.frontend/core/_ParserDecls/enum_module_body.spl") ?? ""
val codegen = rt_file_read_text("src/compiler/70.backend/backend/codegen_types.spl") ?? ""

expect(parser).to_contain("return finalize_decl_visibility(parse_struct_or_trait_decl(false, true), visibility)")
expect(codegen).to_contain("pub trait Codegen:")
```

</details>

#### carries declaration order without calling Dict keys during desugaring

- carries declaration order without calling Dict keys during desugaring
- Verify: carries declaration order without calling Dict keys during desugaring


<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("carries declaration order without calling Dict keys during desugaring")
step("Verify: carries declaration order without calling Dict keys during desugaring")
val module_types = rt_file_read_text("src/compiler/10.frontend/parser_types.spl") ?? ""
val assembly = rt_file_read_text("src/compiler/10.frontend/_FlatAstBridge/module_assembly.spl") ?? ""
val desugar = rt_file_read_text("src/compiler/10.frontend/desugar/desugar_async.spl") ?? ""

expect(module_types).to_contain("function_order: [text]")
expect(module_types).to_contain("actor_order: [text]")
expect(assembly).to_contain("function_order.push(fn_.name)")
expect(desugar).to_contain("val function_names = module.function_order")
expect(desugar).to_contain("val helper_names = generated_helper_names")
expect(desugar).to_contain("val actor_names = module.actor_order")
expect(desugar).to_not_contain("module.functions.keys()")
expect(desugar).to_not_contain("generated_helper_functions.keys()")
expect(desugar).to_not_contain("module.actors.keys()")
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 18 |
| Active scenarios | 18 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-COMPILER`
- `REQ-COMPILER-BOOTSTRAP-001`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `b4181f185285ff627625f7777fe4c853c732b4f709b93ef6321d705cfdc1acce`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `b4181f185285ff627625f7777fe4c853c732b4f709b93ef6321d705cfdc1acce`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `b4181f185285ff627625f7777fe4c853c732b4f709b93ef6321d705cfdc1acce`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **86/100**; effective score: **86/100**; blockers: **0**.

SSpec documentization score: 86/100
source: test/01_unit/compiler/bootstrap/stage4_smoke_gate_spec.spl
mirror: doc/06_spec/01_unit/compiler/bootstrap/stage4_smoke_gate_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/compiler/bootstrap/stage4_smoke_gate_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/compiler/bootstrap/stage4_smoke_gate_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: scope, assumptions/preconditions, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/compiler/bootstrap/stage4_smoke_gate_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 13 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/compiler/bootstrap/stage4_smoke_gate_spec.spl:18:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'keeps diagnostic whole-archive mode out of canonical bootstrap' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/bootstrap/stage4_smoke_gate_spec.spl:27:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'fails bootstrap when the freshly built full CLI cannot execute code' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/bootstrap/stage4_smoke_gate_spec.spl:38:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'gates test lint and duplicate-check on the fresh Stage 4 CLI' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
