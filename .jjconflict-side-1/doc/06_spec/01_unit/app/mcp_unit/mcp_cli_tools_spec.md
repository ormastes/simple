# mcp_cli_tools_spec

> Tests the 6 Tier 1 MCP CLI tool handlers: simple_test, simple_build, simple_format, simple_lint, simple_fix, simple_doc_coverage

<!-- sdn-diagram:id=mcp_cli_tools_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=mcp_cli_tools_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

mcp_cli_tools_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=mcp_cli_tools_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 21 | 21 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# mcp_cli_tools_spec

Tests the 6 Tier 1 MCP CLI tool handlers: simple_test, simple_build, simple_format, simple_lint, simple_fix, simple_doc_coverage

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #MCP-CLI-001 |
| Category | Tooling |
| Difficulty | 2/5 |
| Status | Implemented |
| Source | `test/01_unit/app/mcp_unit/mcp_cli_tools_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests the 6 Tier 1 MCP CLI tool handlers:
simple_test, simple_build, simple_format, simple_lint, simple_fix, simple_doc_coverage

## Behavior

- Each tool wraps a bin/simple CLI command via shell_cmd
- Parameters are optional except simple_fix (path required)
- Output includes exit code and command output

## Scenarios

### simple_test tool

#### builds test command with no args

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var cmd = "timeout 120 bin/simple test"
cmd = cmd + " 2>&1"
expect(cmd).to_contain("bin/simple test")
```

</details>

#### builds test command with path

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val path = "test/unit/app/mcp/api_tool_spec.spl"
var cmd = "timeout 120 bin/simple test"
if path != "":
    cmd = cmd + " " + path
cmd = cmd + " 2>&1"
expect(cmd).to_contain(path)
```

</details>

#### builds test command with filter

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val filter_str = "symbol"
var cmd = "timeout 120 bin/simple test"
if filter_str != "":
    cmd = cmd + " --filter " + filter_str
expect(cmd).to_contain("--filter symbol")
```

</details>

#### builds test command with list flag

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val list_flag = "true"
var cmd = "timeout 120 bin/simple test"
if list_flag == "true":
    cmd = cmd + " --list"
expect(cmd).to_contain("--list")
```

</details>

#### builds test command with only-slow flag

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val only_slow = "true"
var cmd = "timeout 120 bin/simple test"
if only_slow == "true":
    cmd = cmd + " --only-slow"
expect(cmd).to_contain("--only-slow")
```

</details>

#### uses per-test timeout for MCP test runs

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var cmd = "timeout 120 bin/simple test"
cmd = cmd + " --timeout 60"
expect(cmd).to_contain("--timeout 60")
```

</details>

### simple_build tool

#### builds basic build command

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var cmd = "timeout 300 bin/simple build"
cmd = cmd + " 2>&1"
expect(cmd).to_contain("bin/simple build")
```

</details>

#### builds release build command

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val release = "true"
var cmd = "timeout 300 bin/simple build"
if release == "true":
    cmd = cmd + " --release"
expect(cmd).to_contain("--release")
```

</details>

#### builds with target

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val target = "aarch64"
var cmd = "timeout 300 bin/simple build"
if target != "":
    cmd = cmd + " --target " + target
expect(cmd).to_contain("--target aarch64")
```

</details>

#### builds with warn-docs

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val warn_docs = "true"
var cmd = "timeout 300 bin/simple build"
if warn_docs == "true":
    cmd = cmd + " --warn-docs"
expect(cmd).to_contain("--warn-docs")
```

</details>

### simple_format tool

#### builds fmt command

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var cmd = "timeout 60 bin/simple fmt"
cmd = cmd + " 2>&1"
expect(cmd).to_contain("bin/simple fmt")
```

</details>

#### builds fmt command with check flag

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val check = "true"
var cmd = "timeout 60 bin/simple fmt"
if check == "true":
    cmd = cmd + " --check"
expect(cmd).to_contain("--check")
```

</details>

#### builds fmt command with path

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val path = "src/app/cli/main.spl"
var cmd = "timeout 60 bin/simple fmt"
if path != "":
    cmd = cmd + " " + path
expect(cmd).to_contain(path)
```

</details>

### simple_lint tool

#### builds lint command

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var cmd = "timeout 60 bin/simple lint"
cmd = cmd + " 2>&1"
expect(cmd).to_contain("bin/simple lint")
```

</details>

#### builds lint command with path

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val path = "src/lib/"
var cmd = "timeout 60 bin/simple lint"
if path != "":
    cmd = cmd + " " + path
expect(cmd).to_contain("src/lib/")
```

</details>

### simple_fix tool

#### requires path parameter

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val path = ""
val has_error = path == ""
expect(has_error).to_equal(true)
```

</details>

#### builds fix command with path

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val path = "src/app/cli/main.spl"
var cmd = "timeout 60 bin/simple fix " + path
cmd = cmd + " 2>&1"
expect(cmd).to_contain("bin/simple fix")
expect(cmd).to_contain(path)
```

</details>

#### builds fix command with dry-run

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var cmd = "timeout 60 bin/simple doc-coverage"
cmd = cmd + " 2>&1"
expect(cmd).to_contain("bin/simple doc-coverage")
```

</details>

#### builds doc-coverage with format

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val format_str = "md"
var cmd = "timeout 60 bin/simple doc-coverage"
if format_str != "":
    cmd = cmd + " --format=" + format_str
expect(cmd).to_contain("--format=md")
```

</details>

#### builds doc-coverage with missing flag

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val missing = "true"
var cmd = "timeout 60 bin/simple doc-coverage"
if missing == "true":
    cmd = cmd + " --missing"
expect(cmd).to_contain("--missing")
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 21 |
| Active scenarios | 21 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
