# LLM Caret Claude CLI Traceability Specification

The direct Caret trace gate derives its file, LOC, and declaration inventory
from the current `src/app/llm_caret/*.spl` tree. It is a bounded migration map,
not proof that every function in the separate Claude-full parts bin works.

| Scenarios | Executed | Passed | Failed |
|---:|---:|---:|---:|
| 4 | 0 | 0 | 0 |

Runtime execution and docgen remain blocked until a qualified self-hosted
Simple runtime is deployed. The checker itself passed independently on
2026-07-25 with 25/25 files, 7,194/7,194 LOC, and 505/505 declarations.

## Scope and claim boundary

- Requirements: `REQ-LLM-CARET-CLAUDE-TRACE-001..005`
- NFRs: `NFR-LLM-CARET-TRACE-001..004`
- Executable spec:
  `test/03_system/tools/llm/llm_caret_claude_cli_traceability_spec.spl`
- Checker: `scripts/check/check-llm-caret-claude-cli-trace.shs`
- Report: `doc/09_report/llm_caret_claude_cli_traceability.md`
- Exact inventory: `doc/09_report/llm_caret_claude_cli_symbols.tsv`

This gate proves the direct Caret map stays complete for its current 25-file
scope. It does not prove the historical 1,902-file Claude-full inventory,
current upstream parity, live authentication, paid provider calls, or PTY
behavior.

## Scenario flow

### REQ-LLM-CARET-CLAUDE-TRACE-001..002: mapped artifacts

#### should keep the report checker and exact symbol inventory together

1. Confirm every traceability artifact is present.
2. Check the report, checker, and exact inventory paths independently.

<details>
<summary>Executable SSpec</summary>

```simple
step("Confirm every traceability artifact is present")
expect(file_exists(TRACE_REPORT)).to_equal(true)
expect(file_exists(TRACE_CHECK)).to_equal(true)
expect(file_exists(TRACE_SYMBOLS)).to_equal(true)
```

</details>

#### should document MDSOC ownership and both Claude and Simple mappings

1. Inspect the Claude-to-Simple trace report.
2. Check architecture markers and both sides of the migration map.

<details>
<summary>Executable SSpec</summary>

```simple
step("Inspect the Claude-to-Simple trace report")
val report = file_read(TRACE_REPORT)

expect(report).to_contain("## MDSOC+ Caret Boundary")
expect(report).to_contain("## Source File Mapping")
expect(report).to_contain("## Function Trace")
expect(report).to_contain("## Simple Symbol Trace")
expect(report).to_contain("## Claude Source Trace")
expect(report).to_contain("## Claude Key Symbol Trace")
expect(report).to_contain("tmp/claude/claude-code-main/src")
expect(report).to_contain("src/app/llm_caret/claude_cli.spl")
expect(report).to_contain("src/entrypoints/cli.tsx")
expect(report).to_contain("src/QueryEngine.ts")
expect(report).to_contain("class:QueryEngine")
```

</details>

### NFR-LLM-CARET-TRACE-001..004: offline deterministic derivation

#### should derive the inventory offline from files and stable text tools

1. Inspect the trace checker execution boundary.
2. Reject provider/network commands.
3. Require deterministic filesystem, sort, and cleanup primitives.

<details>
<summary>Executable SSpec</summary>

```simple
step("Inspect the trace checker execution boundary")
val source = file_read(TRACE_CHECK)

expect(trace_checker_has_forbidden_network_command(source)).to_equal(false)
expect(source).to_contain("find \"$src_dir\"")
expect(source).to_contain("sort -u")
expect(source).to_contain("mktemp")
expect(source).to_contain("trap")
```

</details>

### REQ-LLM-CARET-CLAUDE-TRACE-003..005: computed closure

#### should pass exact file LOC and declaration coverage for the current caret

1. Run the computed traceability checker once.
2. Check exact file, LOC, declaration, exit, and final status evidence.

<details>
<summary>Executable SSpec</summary>

```simple
step("Run the computed traceability checker once")
val result = run_trace_check()
val output = result.0

expect(result.1).to_equal(0)
expect(output).to_contain("llm_caret_source_files=25")
expect(output).to_contain("llm_caret_mapped_files=25")
expect(output).to_contain("llm_caret_mapping_percent=100")
expect(output).to_contain("llm_caret_source_loc=7194")
expect(output).to_contain("llm_caret_mapped_loc=7194")
expect(output).to_contain("llm_caret_loc_mapping_percent=100")
expect(output).to_contain("llm_caret_symbol_count=505")
expect(output).to_contain("llm_caret_symbol_traced_count=505")
expect(output).to_contain("STATUS: PASS llm-caret-claude-cli-trace")
```

</details>

## Supporting executable helpers

<details>
<summary>Setup and checker source</summary>

```simple
val TRACE_REPORT = "doc/09_report/llm_caret_claude_cli_traceability.md"
val TRACE_CHECK = "scripts/check/check-llm-caret-claude-cli-trace.shs"
val TRACE_SYMBOLS = "doc/09_report/llm_caret_claude_cli_symbols.tsv"

fn run_trace_check() -> (text, i64):
    val (out_text, err_text, exit_code) = process_run("sh", [TRACE_CHECK])
    (out_text + err_text, exit_code)

fn trace_checker_has_forbidden_network_command(source: text) -> bool:
    source.contains("curl ") or source.contains("wget ") or source.contains("claude ")
```

</details>

## Execution

After a qualified self-hosted runtime is available, run exactly once:

```bash
bin/simple test test/03_system/tools/llm/llm_caret_claude_cli_traceability_spec.spl --mode=interpreter
bin/simple spipe-docgen test/03_system/tools/llm/llm_caret_claude_cli_traceability_spec.spl --output doc/06_spec --no-index
```

Do not infer executable PASS from this synchronized zero-execution manual.
