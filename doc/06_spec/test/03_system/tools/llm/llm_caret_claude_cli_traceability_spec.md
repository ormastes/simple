# LLM Caret Claude CLI Traceability Specification

> This system spec proves the Claude CLI migration trace remains current enough to guide hardening work. The checker computes the current `src/app/llm_caret/*.spl` file and LOC mapping coverage, then confirms every current Simple function, struct, and extern symbol appears in the trace table.

<!-- sdn-diagram:id=llm_caret_claude_cli_traceability_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=llm_caret_claude_cli_traceability_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

llm_caret_claude_cli_traceability_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=llm_caret_claude_cli_traceability_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 3 | 3 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# LLM Caret Claude CLI Traceability Specification

This system spec proves the Claude CLI migration trace remains current enough to guide hardening work. The checker computes the current `src/app/llm_caret/*.spl` file and LOC mapping coverage, then confirms every current Simple function, struct, and extern symbol appears in the trace table.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Tooling |
| Status | Implemented |
| Requirements | doc/02_requirements/feature/llm_caret_claude_cli_harden.md |
| Plan | doc/03_plan/sys_test/llm_caret_claude_cli_harden.md |
| Design | doc/05_design/llm_caret_claude_cli_harden.md |
| Research | doc/01_research/local/llm_caret_claude_cli_harden.md |
| Source | `test/03_system/tools/llm/llm_caret_claude_cli_traceability_spec.spl` |
| Updated | 2026-07-05 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

This system spec proves the Claude CLI migration trace remains current enough
to guide hardening work. The checker computes the current
`src/app/llm_caret/*.spl` file and LOC mapping coverage, then confirms every
current Simple function, struct, and extern symbol appears in the trace table.

## Syntax

```bash
sh scripts/check/check-llm-caret-claude-cli-trace.shs
bin/simple test test/03_system/tools/llm/llm_caret_claude_cli_traceability_spec.spl --mode=interpreter
```

## Examples

A passing checker prints `llm_caret_mapping_percent=100`,
`llm_caret_loc_mapping_percent=100`,
`llm_caret_symbol_traced_count=161`, and
`STATUS: PASS llm-caret-claude-cli-trace` for the current mapped caret.

## Workflow

1. Inspect the Claude source tree under `tmp/claude/claude-code-main/src`.
2. Extract feature groups, not copied implementation bodies.
3. Map each Simple source file in `src/app/llm_caret` to a Claude source file
   or to an explicit Simple-only provider extension.
4. Record the mapping in
   `doc/09_report/llm_caret_claude_cli_traceability.md`.
5. Run the checker.
6. Run this SSpec.
7. Regenerate this manual with `bin/simple spipe-docgen`.

## Source Contract

The report must keep these sections:

- `## MDSOC+ Caret Boundary`
- `## Extracted Claude CLI Features`
- `## Source File Mapping`
- `## Function Trace`
- `## Simple Symbol Trace`
- `## Claude Source Trace`
- `## Claude Key Symbol Trace`
- `## Verification`

The mapping table must include every current `src/app/llm_caret/*.spl` file,
and the symbol table must include every current function, struct, and extern
symbol as a backticked `kind:name` token. The checker computes those lists
from the filesystem, so adding a provider file or symbol without trace rows
fails the gate.

## Coverage Rule

The required threshold is 80% mapped files and 80% mapped LOC. A Simple-only
extension still counts when the row says it is Simple-only and names the role.
This keeps non-Claude providers such as OpenCode, OpenAI-compatible endpoints,
and local torch visible without pretending they came from Claude Code.

## MDSOC+ Rule

`src/app/llm_caret` remains one app-layer provider caret. The trace report may
point to runtime or HTTP facades as dependencies, but this lane must not move
runtime ownership into the app caret. Runtime boundary fixes belong in a
separate implementation lane.

## Out Of Scope

The gate does not prove live Claude authentication, remote control, OAuth,
terminal UI parity, or agent orchestration. It proves the migration map and the
offline traceability contract only.

## Failure Handling

If the checker prints `STATUS: FAIL`, inspect the key before editing code:

- `llm_caret_mapping_percent` below 80 means source files were added without
  trace rows.
- `llm_caret_loc_mapping_percent` below 80 means the unmapped files exceed the
  allowed LOC budget.
- `missing_symbol_trace` means a function, struct, or extern exists in source
  without a `kind:name` entry in the Simple Symbol Trace.
- `missing_marker` means the report lost a required operator section.
- `llm_caret_trace_report=missing` means the report path changed or was not
  generated.

Fix the report or checker first, then rerun this SSpec once. Do not bypass the
gate with placeholder rows; each row must name either a Claude source match or
an explicit Simple-only role.

## Operator Checklist

- The checker path exists.
- The report path exists.
- The report names the `tmp/claude/claude-code-main/src` evidence root.
- The report maps `src/app/llm_caret/claude_cli.spl`.
- The report names `src/entrypoints/cli.tsx`.
- The report names `src/QueryEngine.ts`.
- The report names key Claude-side symbols such as `class:QueryEngine`.
- The checker reports source-file count.
- The checker reports mapped-file count.
- The checker reports mapping percent.
- The checker reports source LOC.
- The checker reports mapped LOC.
- The checker reports LOC mapping percent.
- The checker reports symbol count.
- The checker reports traced symbol count.
- The checker reports `STATUS: PASS llm-caret-claude-cli-trace`.

## Evidence Produced

The passing SSpec output proves the trace report and checker are present and
that the checker accepts the current mapping. The checker output records the
current file count and percentage, which is the release evidence for the 80%
mapping gate.

## Scenarios

### LLM caret Claude CLI traceability

#### keeps the trace report and checker in the tree

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(file_exists(TRACE_REPORT)).to_equal(true)
expect(file_exists(TRACE_CHECK)).to_equal(true)
```

</details>

#### documents MDSOC+ ownership and source mappings

<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

#### passes the computed 80 percent mapping gate

<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val output = run_trace_check()

expect(output).to_contain("llm_caret_source_files=")
expect(output).to_contain("llm_caret_mapped_files=")
expect(output).to_contain("llm_caret_mapping_percent=")
expect(output).to_contain("llm_caret_source_loc=")
expect(output).to_contain("llm_caret_mapped_loc=")
expect(output).to_contain("llm_caret_loc_mapping_percent=")
expect(output).to_contain("llm_caret_symbol_count=")
expect(output).to_contain("llm_caret_symbol_traced_count=")
expect(output).to_contain("STATUS: PASS llm-caret-claude-cli-trace")
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 3 |
| Active scenarios | 3 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


## Related Documentation

- **Requirements:** [doc/02_requirements/feature/llm_caret_claude_cli_harden.md](doc/02_requirements/feature/llm_caret_claude_cli_harden.md)
- **Plan:** [doc/03_plan/sys_test/llm_caret_claude_cli_harden.md](doc/03_plan/sys_test/llm_caret_claude_cli_harden.md)
- **Design:** [doc/05_design/llm_caret_claude_cli_harden.md](doc/05_design/llm_caret_claude_cli_harden.md)
- **Research:** [doc/01_research/local/llm_caret_claude_cli_harden.md](doc/01_research/local/llm_caret_claude_cli_harden.md)


</details>
