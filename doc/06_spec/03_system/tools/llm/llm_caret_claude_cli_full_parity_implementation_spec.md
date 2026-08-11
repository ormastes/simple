# LLM Caret Claude CLI Full-Parity Implementation Gate

This is the strict red gate for the full Claude inventory. Historical matrix
rows are not accepted without their provenance-pinned source tree, and existing
Simple targets are not accepted until every mapped file, size, class, and final
status condition passes.

| Scenarios | Executed | Passed | Failed |
|---:|---:|---:|---:|
| 4 | 0 | 0 | 0 |

No executable PASS is claimed. On 2026-07-25 the standalone checkers reported
the expected blockers: the pinned source tree is absent, 1,157 of 1,902 target
files are missing, and 1,302 targets are below the 80% source-size floor.

## Scope and claim boundary

- Requirements: `REQ-LLM-CARET-FULL-001..007`
- NFRs: `NFR-LLM-CARET-FULL-001..005`
- Executable spec:
  `test/03_system/tools/llm/llm_caret_claude_cli_full_parity_implementation_spec.spl`
- Plan checker: `scripts/check/check-llm-caret-full-parity-plan.shs`
- Implementation checker:
  `scripts/check/check-llm-caret-full-parity-implementation.shs`

The public `@anthropic-ai/claude-code@2.1.218` package contains seven package
entries and no `src/` tree, so its binary wrapper is not a substitute for the
required pinned source inventory. Focused Caret tests are valuable incremental
evidence but cannot turn this full-parity gate green.

## Scenario flow

### LLM caret Claude CLI full-parity implementation

#### should keep the plan matrices and checkers available

1. Confirm the generated matrices and checker scripts are present.
2. Keep both the inventory and implementation authorities available.

<details>
<summary>Executable SSpec</summary>

```simple
step("Confirm the generated matrices and checker scripts are present")
expect(file_exists(FILE_MATRIX)).to_be(true)
expect(file_exists(SYMBOL_MATRIX)).to_be(true)
expect(file_exists(PLAN_CHECK)).to_be(true)
expect(file_exists(IMPL_CHECK)).to_be(true)
```

</details>

#### should require the pinned Claude source tree instead of historical rows alone

1. Confirm the provenance-pinned Claude source inventory is present.
2. Fail while only historical matrices remain.

<details>
<summary>Executable SSpec</summary>

```simple
step("Confirm the provenance-pinned Claude source inventory is present")
expect(dir_exists(UPSTREAM_SRC)).to_equal(true)
```

</details>

#### should keep the full-parity plan inventory matched to Claude source

1. Run the plan checker against the Claude source tree and matrices.
2. Require a zero exit plus exact file, feature, and symbol rows.

<details>
<summary>Executable SSpec</summary>

```simple
step("Run the plan checker against the Claude source tree and matrices")
val result = run_check(PLAN_CHECK)
val output = result.0

expect(result.1).to_equal(0)
expect(output).to_contain("claude_source_files=1902")
expect(output).to_contain("full_parity_file_rows=1902")
expect(output).to_contain("full_parity_feature_rows=599")
expect(output).to_contain("full_parity_symbol_rows=14119")
expect(output).to_contain("STATUS: PASS llm-caret-full-parity-plan")
```

</details>

#### should prove mapped files and Claude classes reach implementation parity

1. Run the strict implementation checker once for file, size, and class parity.
2. Check class rows resolve to implemented Simple target files.
3. Require zero missing/undersized targets and the final PASS marker.

<details>
<summary>Executable SSpec</summary>

```simple
step("Run the strict implementation checker once for file, size, and class parity")
val result = run_check(IMPL_CHECK)
val output = result.0

expect(result.1).to_equal(0)
expect(output).to_contain("file_rows=1902")
expect(output).to_contain("target_files_missing=0")
expect(output).to_contain("target_loc_lt_80pct_source=0")
expect(output).to_contain("target_loc_ge_required=1902")
step("Check class rows resolve to implemented Simple target files")
expect(output).to_contain("class_rows=124")
expect(output).to_contain("class_target_files_missing=0")
expect(output).to_contain("STATUS: PASS llm-caret-full-parity-implementation")
```

</details>

## Supporting executable helpers

<details>
<summary>Paths and checker source</summary>

```simple
val PLAN_CHECK = "scripts/check/check-llm-caret-full-parity-plan.shs"
val IMPL_CHECK = "scripts/check/check-llm-caret-full-parity-implementation.shs"
val FILE_MATRIX = "doc/03_plan/trace/llm_caret_claude_cli_full_parity_file_matrix.tsv"
val SYMBOL_MATRIX = "doc/03_plan/trace/llm_caret_claude_cli_full_parity_symbol_matrix.tsv"
val UPSTREAM_SRC = "tmp/claude/claude-code-main/src"

fn run_check(path: text) -> (text, i64):
    val (out_text, err_text, exit_code) = process_run("sh", [path])
    (out_text + err_text, exit_code)
```

</details>

## Execution

After the pinned source tree and qualified self-hosted runtime exist, run each
checker and SSpec once. A missing tree, nonzero checker exit, or missing PASS
marker remains a failure:

```bash
sh scripts/check/check-llm-caret-full-parity-plan.shs
sh scripts/check/check-llm-caret-full-parity-implementation.shs
bin/simple test test/03_system/tools/llm/llm_caret_claude_cli_full_parity_implementation_spec.spl --mode=interpreter
```

Do not infer executable PASS from this synchronized zero-execution manual.
