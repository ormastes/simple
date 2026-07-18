# Mcpgdb Log Modes Specification

> <details>

<!-- sdn-diagram:id=mcpgdb_log_modes_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=mcpgdb_log_modes_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

mcpgdb_log_modes_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=mcpgdb_log_modes_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 6 | 6 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Mcpgdb Log Modes Specification

## Scenarios

### mcpgdb log mode CLI options

#### shows shared log options in help

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val (out, err, code) = _run_mcpgdb(["--help"])
expect(code).to_equal(0)
expect(out).to_contain("mcpgdb MCP Server")
expect(out).to_contain("--log-mode")
expect(out).to_contain("--progress")
```

</details>

#### supports log-mode json ready output

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val (out, err, code) = _run_mcpgdb(["--log-mode=json"])
expect(code).to_equal(0)
expect(out).to_contain("\"command\":\"mcpgdb\"")
expect(out).to_contain("\"status\":\"ready\"")
```

</details>

#### supports dot progress for help output

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val (out, err, code) = _run_mcpgdb(["--progress=dot", "--help"])
expect(code).to_equal(0)
expect(out).to_contain(".\nmcpgdb MCP Server")
```

</details>

#### rejects invalid log mode

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val (out, err, code) = _run_mcpgdb(["--log-mode=noisy"])
expect(code).to_equal(1)
```

</details>

#### renders json unknown option output

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val (out, err, code) = _run_mcpgdb(["--log-mode=json", "--surprise"])
expect(code).to_equal(1)
expect(out).to_contain("\"status\":\"error\"")
expect(out).to_contain("Unknown mcpgdb option: --surprise")
```

</details>

#### preserves normal MCP ping handling

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val (out, err, code) = _ping_mcpgdb()
expect(code).to_equal(0)
expect(out).to_contain("\"jsonrpc\":\"2.0\"")
expect(out).to_contain("\"result\":{}")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/02_integration/app/mcpgdb_log_modes_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- mcpgdb log mode CLI options

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 6 |
| Active scenarios | 6 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
