# Mcp Cli Tools Specification

> Tests covering simple_test tool, simple_build tool, simple_format tool, simple_lint tool, simple_fix tool, simple_doc_coverage tool.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 21 | 21 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Mcp Cli Tools Specification

## Scenarios

### simple_test tool

#### builds test command with no args

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- builds test command with no args


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("builds test command with no args")
var cmd = "timeout 120 bin/simple test"
cmd = cmd + " 2>&1"
expect(cmd).to_contain("bin/simple test")
```

</details>

#### builds test command with path

- builds test command with path


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("builds test command with path")
val path = "test/unit/app/mcp/api_tool_spec.spl"
var cmd = "timeout 120 bin/simple test"
if path != "":
    cmd = cmd + " " + path
cmd = cmd + " 2>&1"
expect(cmd).to_contain(path)
```

</details>

#### builds test command with filter

- builds test command with filter


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("builds test command with filter")
val filter_str = "symbol"
var cmd = "timeout 120 bin/simple test"
if filter_str != "":
    cmd = cmd + " --filter " + filter_str
expect(cmd).to_contain("--filter symbol")
```

</details>

#### builds test command with list flag

- builds test command with list flag


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("builds test command with list flag")
val list_flag = "true"
var cmd = "timeout 120 bin/simple test"
if list_flag == "true":
    cmd = cmd + " --list"
expect(cmd).to_contain("--list")
```

</details>

#### builds test command with only-slow flag

- builds test command with only-slow flag


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("builds test command with only-slow flag")
val only_slow = "true"
var cmd = "timeout 120 bin/simple test"
if only_slow == "true":
    cmd = cmd + " --only-slow"
expect(cmd).to_contain("--only-slow")
```

</details>

#### uses per-test timeout for MCP test runs

- uses per-test timeout for MCP test runs


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("uses per-test timeout for MCP test runs")
var cmd = "timeout 120 bin/simple test"
cmd = cmd + " --timeout 60"
expect(cmd).to_contain("--timeout 60")
```

</details>

### simple_build tool

#### builds basic build command

- builds basic build command


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("builds basic build command")
var cmd = "timeout 300 bin/simple build"
cmd = cmd + " 2>&1"
expect(cmd).to_contain("bin/simple build")
```

</details>

#### builds release build command

- builds release build command


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("builds release build command")
val release = "true"
var cmd = "timeout 300 bin/simple build"
if release == "true":
    cmd = cmd + " --release"
expect(cmd).to_contain("--release")
```

</details>

#### builds with target

- builds with target


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("builds with target")
val target = "aarch64"
var cmd = "timeout 300 bin/simple build"
if target != "":
    cmd = cmd + " --target " + target
expect(cmd).to_contain("--target aarch64")
```

</details>

#### builds with warn-docs

- builds with warn-docs


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("builds with warn-docs")
val warn_docs = "true"
var cmd = "timeout 300 bin/simple build"
if warn_docs == "true":
    cmd = cmd + " --warn-docs"
expect(cmd).to_contain("--warn-docs")
```

</details>

### simple_format tool

#### builds fmt command

- builds fmt command


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("builds fmt command")
var cmd = "timeout 60 bin/simple fmt"
cmd = cmd + " 2>&1"
expect(cmd).to_contain("bin/simple fmt")
```

</details>

#### builds fmt command with check flag

- builds fmt command with check flag


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("builds fmt command with check flag")
val check = "true"
var cmd = "timeout 60 bin/simple fmt"
if check == "true":
    cmd = cmd + " --check"
expect(cmd).to_contain("--check")
```

</details>

#### builds fmt command with path

- builds fmt command with path


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("builds fmt command with path")
val path = "src/app/cli/main.spl"
var cmd = "timeout 60 bin/simple fmt"
if path != "":
    cmd = cmd + " " + path
expect(cmd).to_contain(path)
```

</details>

### simple_lint tool

#### builds lint command

- builds lint command


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("builds lint command")
var cmd = "timeout 60 bin/simple lint"
cmd = cmd + " 2>&1"
expect(cmd).to_contain("bin/simple lint")
```

</details>

#### builds lint command with path

- builds lint command with path


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("builds lint command with path")
val path = "src/lib/"
var cmd = "timeout 60 bin/simple lint"
if path != "":
    cmd = cmd + " " + path
expect(cmd).to_contain("src/lib/")
```

</details>

### simple_fix tool

#### requires path parameter

- requires path parameter
   - Expected: has_error is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("requires path parameter")
val path = ""
val has_error = path == ""
expect(has_error).to_equal(true)
```

</details>

#### builds fix command with path

- builds fix command with path


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("builds fix command with path")
val path = "src/app/cli/main.spl"
var cmd = "timeout 60 bin/simple fix " + path
cmd = cmd + " 2>&1"
expect(cmd).to_contain("bin/simple fix")
expect(cmd).to_contain(path)
```

</details>

#### builds fix command with dry-run

- builds fix command with dry-run


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("builds fix command with dry-run")
val path = "src/app/cli/main.spl"
val dry_run = "true"
var cmd = "timeout 60 bin/simple fix " + path
if dry_run == "true":
    cmd = cmd + " --dry-run"
expect(cmd).to_contain("--dry-run")
```

</details>

### simple_doc_coverage tool

#### builds doc-coverage command

- builds doc-coverage command


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("builds doc-coverage command")
var cmd = "timeout 60 bin/simple doc-coverage"
cmd = cmd + " 2>&1"
expect(cmd).to_contain("bin/simple doc-coverage")
```

</details>

#### builds doc-coverage with format

- builds doc-coverage with format


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("builds doc-coverage with format")
val format_str = "md"
var cmd = "timeout 60 bin/simple doc-coverage"
if format_str != "":
    cmd = cmd + " --format=" + format_str
expect(cmd).to_contain("--format=md")
```

</details>

#### builds doc-coverage with missing flag

- builds doc-coverage with missing flag


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("builds doc-coverage with missing flag")
val missing = "true"
var cmd = "timeout 60 bin/simple doc-coverage"
if missing == "true":
    cmd = cmd + " --missing"
expect(cmd).to_contain("--missing")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/unit/app/mcp_unit/mcp_cli_tools_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering simple_test tool, simple_build tool, simple_format tool, simple_lint tool, simple_fix tool, simple_doc_coverage tool.
- simple_test tool
- simple_build tool
- simple_format tool
- simple_lint tool
- simple_fix tool
- simple_doc_coverage tool

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 21 |
| Active scenarios | 21 |
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

- Canonical SPipe generation for source `a17b3931224a005343455ebd86ec4ba5eb387b82a141bfb362ca173eab6cebed`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `a17b3931224a005343455ebd86ec4ba5eb387b82a141bfb362ca173eab6cebed`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `a17b3931224a005343455ebd86ec4ba5eb387b82a141bfb362ca173eab6cebed`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/unit/app/mcp_unit/mcp_cli_tools_spec.spl
mirror: doc/06_spec/unit/app/mcp_unit/mcp_cli_tools_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/unit/app/mcp_unit/mcp_cli_tools_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/unit/app/mcp_unit/mcp_cli_tools_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/unit/app/mcp_unit/mcp_cli_tools_spec.spl:32:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'builds test command with no args' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/app/mcp_unit/mcp_cli_tools_spec.spl:39:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'builds test command with path' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/app/mcp_unit/mcp_cli_tools_spec.spl:49:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'builds test command with filter' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
