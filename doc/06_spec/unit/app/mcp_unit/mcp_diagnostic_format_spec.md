# Mcp Diagnostic Format Specification

> Tests covering MCP Diagnostic Format.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 12 | 12 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Mcp Diagnostic Format Specification

## Scenarios

### MCP Diagnostic Format

#### strip_ansi
_Removes ANSI escape codes from text_

#### passes through plain text

- passes through plain text
   - Expected: strip_ansi("hello world") equals `hello world`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("passes through plain text")
expect(strip_ansi("hello world")).to_equal("hello world")
```

</details>

#### returns empty for empty input

- returns empty for empty input
   - Expected: strip_ansi("") equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns empty for empty input")
expect(strip_ansi("")).to_equal("")
```

</details>

#### parse_diag_text_line
_Parses text diagnostic lines into formatted strings_

#### parses error line

- parses error line


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("parses error line")
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

- parses warning line


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("parses warning line")
val line = "src/test.spl:20:1: warning: unused import"
val result = parse_diag_text_line(line)
expect(result).to_contain("Warning")
expect(result).to_contain("line 20")
expect(result).to_contain("unused import")
```

</details>

#### returns empty for non-diagnostic line

- returns empty for non-diagnostic line
   - Expected: result equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns empty for non-diagnostic line")
val line = "Checking src/test.spl... OK"
val result = parse_diag_text_line(line)
expect(result).to_equal("")
```

</details>

#### returns empty for empty line

- returns empty for empty line
   - Expected: parse_diag_text_line("") equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns empty for empty line")
expect(parse_diag_text_line("")).to_equal("")
```

</details>

#### returns empty for summary line

- returns empty for summary line
   - Expected: result equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns empty for summary line")
val line = "1 error(s) found in 1 file(s)"
val result = parse_diag_text_line(line)
expect(result).to_equal("")
```

</details>

#### format_new_diagnostics_block
_Produces <new-diagnostics> block from check output_

#### returns empty for no diagnostics

- returns empty for no diagnostics
   - Expected: result equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns empty for no diagnostics")
val result = format_new_diagnostics_block("test.spl", "")
expect(result).to_equal("")
```

</details>

#### returns empty for clean output

- returns empty for clean output
   - Expected: result equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns empty for clean output")
val result = format_new_diagnostics_block("test.spl", "Checking test.spl... OK\nAll checks passed")
expect(result).to_equal("")
```

</details>

#### wraps single error in block

- wraps single error in block


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("wraps single error in block")
val output = "src/test.spl:10:5: error: unexpected token\n  expected: expression\n  found:    Colon"
val result = format_new_diagnostics_block("src/test.spl", output)
expect(result).to_contain("<new-diagnostics>")
expect(result).to_contain("</new-diagnostics>")
expect(result).to_contain("src/test.spl:")
expect(result).to_contain("Error (line 10, col 5)")
```

</details>

#### wraps multiple diagnostics in block

- wraps multiple diagnostics in block


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("wraps multiple diagnostics in block")
val output = "test.spl:10:1: error: parse error\ntest.spl:20:1: warning: unused var"
val result = format_new_diagnostics_block("test.spl", output)
expect(result).to_contain("Error (line 10")
expect(result).to_contain("Warning (line 20")
```

</details>

#### skips non-diagnostic lines

- skips non-diagnostic lines


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("skips non-diagnostic lines")
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
| Source | `test/unit/app/mcp_unit/mcp_diagnostic_format_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering MCP Diagnostic Format.
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

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-UNIT`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `4261f9d75def1f8f25dce292b22d903f6716efb26e543615650270bed7889654`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `4261f9d75def1f8f25dce292b22d903f6716efb26e543615650270bed7889654`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `4261f9d75def1f8f25dce292b22d903f6716efb26e543615650270bed7889654`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/unit/app/mcp_unit/mcp_diagnostic_format_spec.spl
mirror: doc/06_spec/unit/app/mcp_unit/mcp_diagnostic_format_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/unit/app/mcp_unit/mcp_diagnostic_format_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/unit/app/mcp_unit/mcp_diagnostic_format_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/unit/app/mcp_unit/mcp_diagnostic_format_spec.spl:25:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'passes through plain text' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/app/mcp_unit/mcp_diagnostic_format_spec.spl:30:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'returns empty for empty input' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/app/mcp_unit/mcp_diagnostic_format_spec.spl:38:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'parses error line' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
