# Mcp Query Tools Specification

> Tests covering simple_definition tool, simple_references tool, simple_hover tool, simple_completions tool, simple_type_at tool.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 9 | 9 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Mcp Query Tools Specification

## Scenarios

### simple_definition tool

#### requires file parameter

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- requires file parameter
   - Expected: has_error is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("requires file parameter")
val file = ""
val has_error = file == ""
expect(has_error).to_equal(true)
```

</details>

#### requires line parameter

- requires line parameter
   - Expected: has_error is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("requires line parameter")
val line = ""
val has_error = line == ""
expect(has_error).to_equal(true)
```

</details>

#### builds definition command

- builds definition command


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("builds definition command")
val file = "src/app/cli/main.spl"
val line = "42"
var cmd = "timeout 30 bin/simple query definition " + file + " " + line
cmd = cmd + " 2>&1"
expect(cmd).to_contain("query definition")
expect(cmd).to_contain(file)
expect(cmd).to_contain(line)
```

</details>

#### builds definition command with column

- builds definition command with column


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("builds definition command with column")
val file = "src/app/cli/main.spl"
val line = "42"
val column = "10"
var cmd = "timeout 30 bin/simple query definition " + file + " " + line
if column != "":
    cmd = cmd + " " + column
expect(cmd).to_contain("42 10")
```

</details>

### simple_references tool

#### builds references command

- builds references command


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("builds references command")
val file = "src/app/cli/main.spl"
val line = "42"
var cmd = "timeout 30 bin/simple query references " + file + " " + line
cmd = cmd + " 2>&1"
expect(cmd).to_contain("query references")
```

</details>

### simple_hover tool

#### builds hover command

- builds hover command


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("builds hover command")
val file = "src/app/cli/main.spl"
val line = "42"
var cmd = "timeout 30 bin/simple query hover " + file + " " + line
cmd = cmd + " 2>&1"
expect(cmd).to_contain("query hover")
```

</details>

### simple_completions tool

#### builds completions command

- builds completions command


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("builds completions command")
val file = "src/app/cli/main.spl"
val line = "42"
var cmd = "timeout 30 bin/simple query completions " + file + " " + line
cmd = cmd + " 2>&1"
expect(cmd).to_contain("query completions")
```

</details>

#### builds completions command with prefix

- builds completions command with prefix


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("builds completions command with prefix")
val file = "src/app/cli/main.spl"
val line = "42"
val prefix = "cli_"
var cmd = "timeout 30 bin/simple query completions " + file + " " + line
if prefix != "":
    cmd = cmd + " --prefix " + prefix
expect(cmd).to_contain("--prefix cli_")
```

</details>

### simple_type_at tool

#### builds type-at command

- builds type-at command


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("builds type-at command")
val file = "src/app/cli/main.spl"
val line = "42"
var cmd = "timeout 30 bin/simple query type-at " + file + " " + line
cmd = cmd + " 2>&1"
expect(cmd).to_contain("query type-at")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/unit/app/mcp_unit/mcp_query_tools_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering simple_definition tool, simple_references tool, simple_hover tool, simple_completions tool, simple_type_at tool.
- simple_definition tool
- simple_references tool
- simple_hover tool
- simple_completions tool
- simple_type_at tool

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 9 |
| Active scenarios | 9 |
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

- Canonical SPipe generation for source `707e72a39f0316bff701d613f699a7b7b20b703b5d153638a73b702483b537e7`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `707e72a39f0316bff701d613f699a7b7b20b703b5d153638a73b702483b537e7`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `707e72a39f0316bff701d613f699a7b7b20b703b5d153638a73b702483b537e7`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/unit/app/mcp_unit/mcp_query_tools_spec.spl
mirror: doc/06_spec/unit/app/mcp_unit/mcp_query_tools_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/unit/app/mcp_unit/mcp_query_tools_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/unit/app/mcp_unit/mcp_query_tools_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/unit/app/mcp_unit/mcp_query_tools_spec.spl:32:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'requires file parameter' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/app/mcp_unit/mcp_query_tools_spec.spl:39:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'requires line parameter' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/app/mcp_unit/mcp_query_tools_spec.spl:46:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'builds definition command' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
