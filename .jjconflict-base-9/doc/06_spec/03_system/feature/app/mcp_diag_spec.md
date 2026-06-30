# MCP Virtual Diagnostic Tools

> Tests the MCP virtual diagnostic tools for inspecting compiler and runtime state. Verifies that diagnostic queries return accurate information about types, symbols, and compilation artifacts through the MCP protocol interface.

<!-- sdn-diagram:id=mcp_diag_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=mcp_diag_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

mcp_diag_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=mcp_diag_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 3 | 3 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# MCP Virtual Diagnostic Tools

Tests the MCP virtual diagnostic tools for inspecting compiler and runtime state. Verifies that diagnostic queries return accurate information about types, symbols, and compilation artifacts through the MCP protocol interface.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | In Progress |
| Source | `test/03_system/feature/app/mcp_diag_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests the MCP virtual diagnostic tools for inspecting compiler and runtime state.
Verifies that diagnostic queries return accurate information about types, symbols,
and compilation artifacts through the MCP protocol interface.

## Scenarios

### MCP Virtual Diagnostic Tools

#### keeps diagnostic core parsing and result models available

<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = diag_source("diag_core.spl")

expect(source).to_contain("class DiagEntry:")
expect(source).to_contain("class DiagResult:")
expect(source).to_contain("class DiagDelta:")
expect(source).to_contain("fn run_diagnostics(path: text) -> DiagResult")
expect(source).to_contain("fn parse_diag_output(output: text, exit_code: i64, path: text) -> [DiagEntry]")
expect(source).to_contain("error[")
expect(source).to_contain("warning[")
```

</details>

#### keeps read-only diagnostic tool schemas and handlers available

<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = diag_source("diag_read_tools.spl")

expect(source).to_contain("fn schema_simple_read() -> text")
expect(source).to_contain("fn schema_simple_check() -> text")
expect(source).to_contain("fn schema_simple_diagnostics() -> text")
expect(source).to_contain("fn schema_simple_symbols() -> text")
expect(source).to_contain("fn schema_simple_status() -> text")
expect(source).to_contain("fn handle_simple_read(id: text, body: text) -> text")
expect(source).to_contain("fn handle_simple_diagnostics(id: text, body: text) -> text")
```

</details>

#### keeps edit and run diagnostic delta tool surfaces available

<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = diag_source("diag_edit_tools.spl")

expect(source).to_contain("fn schema_simple_edit() -> text")
expect(source).to_contain("fn schema_simple_multi_edit() -> text")
expect(source).to_contain("fn schema_simple_run() -> text")
expect(source).to_contain("fn handle_simple_edit(id: text, body: text) -> text")
expect(source).to_contain("fn handle_simple_multi_edit(id: text, body: text) -> text")
expect(source).to_contain("compute_delta(baseline.entries, current.entries)")
expect(source).to_contain("format_delta_text(delta)")
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


</details>
