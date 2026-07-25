# Mcp T32 Run Guard Specification

> <details>

<!-- sdn-diagram:id=mcp_t32_run_guard_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=mcp_t32_run_guard_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

mcp_t32_run_guard_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=mcp_t32_run_guard_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 21 | 21 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Mcp T32 Run Guard Specification

## Scenarios

### T32 MCP Run Guard

#### always-allowed tools

#### allows sessions_list while running

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(guard_is_always_allowed("t32_sessions_list")).to_equal(true)
```

</details>

#### allows session_open while running

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(guard_is_always_allowed("t32_session_open")).to_equal(true)
```

</details>

#### allows window_list while running

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(guard_is_always_allowed("t32_window_list")).to_equal(true)
```

</details>

#### allows history_tail while running

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(guard_is_always_allowed("t32_history_tail")).to_equal(true)
```

</details>

#### allows cmm_commands while running

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(guard_is_always_allowed("t32_cmm_commands")).to_equal(true)
```

</details>

#### blocked tools

#### blocks window_capture while running

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(guard_is_always_allowed("t32_window_capture")).to_equal(false)
```

</details>

#### blocks screenshot while running

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(guard_is_always_allowed("t32_screenshot")).to_equal(false)
```

</details>

#### blocks field_set while running

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(guard_is_always_allowed("t32_field_set")).to_equal(false)
```

</details>

#### safe cmd_run commands

#### allows Break command

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(guard_is_safe_cmd("Break")).to_equal(true)
```

</details>

#### allows Break.Set command

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(guard_is_safe_cmd("Break.Set main")).to_equal(true)
```

</details>

#### allows Break.Delete command

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(guard_is_safe_cmd("Break.Delete /ALL")).to_equal(true)
```

</details>

#### blocks Data.dump command

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(guard_is_safe_cmd("Data.dump")).to_equal(false)
```

</details>

#### safe eval expressions

#### allows STATE.RUN()

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(guard_is_safe_eval("STATE.RUN()")).to_equal(true)
```

</details>

#### allows PRACTICE.STATE()

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(guard_is_safe_eval("PRACTICE.STATE()")).to_equal(true)
```

</details>

#### blocks Register(PC)

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(guard_is_safe_eval("Register(PC)")).to_equal(false)
```

</details>

#### timeout configuration

#### returns cmm_run timeout

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(guard_get_timeout("t32_cmm_run")).to_equal(60000)
```

</details>

#### returns eval timeout

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(guard_get_timeout("t32_eval")).to_equal(3000)
```

</details>

#### returns default for unknown tool

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(guard_get_timeout("t32_unknown_tool")).to_equal(10000)
```

</details>

#### error message format

#### T4100 includes tool name

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val msg = guard_err_target_running("t32_window_capture")
expect(msg).to_start_with("T4100")
expect(msg).to_contain("t32_window_capture")
expect(msg).to_contain("halted CPU")
```

</details>

#### T4101 includes timeout

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val msg = guard_err_command_timeout("t32_eval", 3000)
expect(msg).to_start_with("T4101")
expect(msg).to_contain("3000")
```

</details>

#### T4100 suggests Break command

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val msg = guard_err_target_running("t32_field_set")
expect(msg).to_contain("Break")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/01_unit/app/mcp_t32/mcp_t32_run_guard_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- T32 MCP Run Guard

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 21 |
| Active scenarios | 21 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
