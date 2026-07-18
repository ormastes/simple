# Mcp Diagnostic Format Specification

> _Tests for structured diagnostic formatting in MCP tool results_

<!-- sdn-diagram:id=mcp_diagnostic_format_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=mcp_diagnostic_format_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

mcp_diagnostic_format_spec -> app
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=mcp_diagnostic_format_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 12 | 12 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Mcp Diagnostic Format Specification

## Scenarios

### MCP Diagnostic Format
_Tests for structured diagnostic formatting in MCP tool results_

#### strip_ansi
_Removes ANSI escape codes from text_

#### passes through plain text

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(strip_ansi("hello world")).to_equal("hello world")
```

</details>

#### returns empty for empty input

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(strip_ansi("")).to_equal("")
```

</details>

#### parse_diag_text_line
_Parses text diagnostic lines into formatted strings_

#### parses error line

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val line = "src/test.spl:10:5: error: undeclared variable"
val result = parse_diag_text_line(line)
expect(result).to_contain("Error")
expect(result).to_contain("line 10")
expect(result).to_contain("col 5")
expect(result).to_contain("undeclared variable")
expect(result).to_contain("(simple)")
```

</details>

#### parses warning line

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val line = "src/test.spl:20:1: warning: unused import"
val result = parse_diag_text_line(line)
expect(result).to_contain("Warning")
expect(result).to_contain("line 20")
expect(result).to_contain("unused import")
```

</details>

#### returns empty for non-diagnostic line

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val line = "Checking src/test.spl... OK"
val result = parse_diag_text_line(line)
expect(result).to_equal("")
```

</details>

#### returns empty for empty line

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(parse_diag_text_line("")).to_equal("")
```

</details>

#### returns empty for summary line

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val line = "1 error(s) found in 1 file(s)"
val result = parse_diag_text_line(line)
expect(result).to_equal("")
```

</details>

#### format_new_diagnostics_block
_Produces <new-diagnostics> block from check output_

#### returns empty for no diagnostics

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = format_new_diagnostics_block("test.spl", "")
expect(result).to_equal("")
```

</details>

#### returns empty for clean output

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = format_new_diagnostics_block("test.spl", "Checking test.spl... OK\nAll checks passed")
expect(result).to_equal("")
```

</details>

#### wraps single error in block

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val output = "src/test.spl:10:5: error: unexpected token\n  expected: expression\n  found:    Colon"
val result = format_new_diagnostics_block("src/test.spl", output)
expect(result).to_contain("<new-diagnostics>")
expect(result).to_contain("</new-diagnostics>")
expect(result).to_contain("src/test.spl:")
expect(result).to_contain("Error (line 10, col 5)")
```

</details>

#### wraps multiple diagnostics in block

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val output = "test.spl:10:1: error: parse error\ntest.spl:20:1: warning: unused var"
val result = format_new_diagnostics_block("test.spl", output)
expect(result).to_contain("Error (line 10")
expect(result).to_contain("Warning (line 20")
```

</details>

#### skips non-diagnostic lines

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val output = "Checking test.spl...\ntest.spl:5:1: error: bad\n1 error(s)"
val result = format_new_diagnostics_block("test.spl", output)
expect(result).to_contain("<new-diagnostics>")
expect(result).to_contain("Error (line 5")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/01_unit/app/mcp_unit/mcp_diagnostic_format_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- MCP Diagnostic Format

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 12 |
| Active scenarios | 12 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
