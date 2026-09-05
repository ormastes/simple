# T32 MCP Runtime Guard Tests

> Guards against T32 MCP server runtime failures: `rt_time_now_unix_micros() / 1000` wrapper must use `stdout_write()` instead

<!-- sdn-diagram:id=t32_mcp_runtime_guard_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=t32_mcp_runtime_guard_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

t32_mcp_runtime_guard_spec -> app
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=t32_mcp_runtime_guard_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 16 | 16 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# T32 MCP Runtime Guard Tests

Guards against T32 MCP server runtime failures: `rt_time_now_unix_micros() / 1000` wrapper must use `stdout_write()` instead

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #T32-MCP-RUNTIME-001 |
| Category | Tooling |
| Difficulty | 2/5 |
| Status | Implemented |
| Requirements | N/A |
| Plan | N/A |
| Source | `test/03_system/feature/app/t32_tools/t32_mcp_runtime_guard_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Guards against T32 MCP server runtime failures:
- Bug 11: `rt_time_ms()` missing in native runtime — replaced with
  `rt_time_now_unix_micros() / 1000` wrapper
- Bug 12: Process hangs silently — debug mode default flipped to ON
- Bug 13: `rt_file_append_text("/proc/self/fd/1")` fails for stdout —
  must use `stdout_write()` instead
- Guard: All extern fns used by T32 MCP modules must exist in native runtime

## Source

- `examples/10_tooling/trace32_tools/t32_mcp/job_manager.spl`
- `examples/10_tooling/trace32_tools/t32_mcp/snapshot_store.spl`
- `examples/10_tooling/trace32_tools/t32_mcp/frontend_cold.spl`
- `examples/10_tooling/trace32_tools/t32_mcp/protocol.spl`

## Scenarios

### Bug 11 — rt_time_ms native availability

#### rt_time_now_unix_micros (actual runtime function)

#### returns a positive value

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val micros = rt_time_now_unix_micros()
expect(micros > 0).to_equal(true)
```

</details>

#### returns a plausible epoch timestamp

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# After 2024-01-01 in microseconds = 1_704_067_200_000_000
val micros = rt_time_now_unix_micros()
expect(micros > 1704067200000000).to_equal(true)
```

</details>

#### rt_time_ms (wrapper in job_manager)

#### returns a positive value

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val ms = rt_time_ms()
expect(ms > 0).to_equal(true)
```

</details>

#### is roughly micros / 1000

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val micros = rt_time_now_unix_micros()
val ms = rt_time_ms()
# Should be within 1 second of each other
val diff = ms - (micros / 1000)
expect(diff > -1000).to_equal(true)
expect(diff < 1000).to_equal(true)
```

</details>

### Bug 12 — debug mode defaults to ON

#### t32_debug_enabled (frontend_cold)

#### returns true when T32_MCP_DEBUG_LOG is unset

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# When the env var is not set, debug should default to ON
# so that silent hangs produce stderr output
val enabled = t32_debug_enabled()
expect(enabled).to_equal(true)
```

</details>

### Bug 13 — stdout_write extern exists

#### stdout_write extern fn

#### is callable and returns non-negative

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Writing an empty string should succeed (return >= 0)
val result = stdout_write("")
expect(result >= 0).to_equal(true)
```

</details>

#### rt_stdout_flush extern fn

#### is callable

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = rt_stdout_flush()
# flush returns 0 on success
expect(result >= 0).to_equal(true)
```

</details>

### T32 MCP extern fn guard — prevents missing-function bugs

#### I/O functions

#### stderr_write exists

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val r = stderr_write("")
expect(r >= 0).to_equal(true)
```

</details>

#### stderr_flush exists

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val r = stderr_flush()
expect(r >= 0).to_equal(true)
```

</details>

#### environment functions

#### rt_env_get exists

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val home = rt_env_get("HOME") ?? ""
# Should return something (or empty), not crash
expect(home.len() >= 0).to_equal(true)
```

</details>

#### rt_env_cwd exists

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val cwd = rt_env_cwd()
expect(cwd.len() > 0).to_equal(true)
```

</details>

#### file I/O functions

#### rt_file_exists exists

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# /tmp always exists on Linux
val found = rt_file_exists("/tmp")
expect(found).to_equal(true)
```

</details>

#### rt_file_write_text exists

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val path = "/tmp/t32_mcp_test_guard_write.txt"
val ok = rt_file_write_text(path, "guard_test")
expect(ok).to_equal(true)
```

</details>

#### rt_file_append_text exists

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val path = "/tmp/t32_mcp_test_guard_write.txt"
val ok = rt_file_append_text(path, "\nappend_test")
expect(ok).to_equal(true)
```

</details>

#### process functions

#### rt_process_run exists

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val (stdout, stderr, code) = rt_process_run("/bin/echo", ["guard_test"])
expect(code).to_equal(0)
expect(stdout).to_contain("guard_test")
```

</details>

#### time functions

#### rt_time_now_unix_micros exists and returns epoch

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val micros = rt_time_now_unix_micros()
expect(micros > 1704067200000000).to_equal(true)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 16 |
| Active scenarios | 16 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
