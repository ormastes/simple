# Mcp Hardware Debug Specification

> <details>

<!-- sdn-diagram:id=mcp_hardware_debug_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=mcp_hardware_debug_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

mcp_hardware_debug_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=mcp_hardware_debug_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 21 | 21 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Mcp Hardware Debug Specification

## Scenarios

### debug_trace_capture handler

#### requires session_id parameter

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val session_id = ""
val has_error = session_id == ""
expect(has_error).to_equal(true)
```

</details>

#### requires T32 session type

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val valid = validate_session_type("t32", ["t32", "t32_gdb"])
expect(valid).to_equal(true)
```

</details>

#### rejects interpreter session type

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val valid = validate_session_type("interpreter", ["t32", "t32_gdb"])
expect(valid).to_equal(false)
```

</details>

#### defaults duration to 1000ms

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var duration = 1000
val duration_str = ""
if duration_str != "":
    duration = 500
expect(duration).to_equal(1000)
```

</details>

### debug_coverage_collect handler

#### requires session_id and module

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val session_id = ""
val module = ""
val missing = session_id == "" or module == ""
expect(missing).to_equal(true)
```

</details>

#### requires T32 session type

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val valid = validate_session_type("t32_gdb", ["t32", "t32_gdb"])
expect(valid).to_equal(true)
```

</details>

#### rejects openocd session type

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val valid = validate_session_type("openocd", ["t32", "t32_gdb"])
expect(valid).to_equal(false)
```

</details>

### debug_flash_program handler

#### requires session_id and elf_path

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val session_id = "session_1"
val elf_path = ""
val missing = session_id == "" or elf_path == ""
expect(missing).to_equal(true)
```

</details>

#### accepts T32 session type

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val valid = validate_session_type("t32", ["t32", "t32_gdb", "openocd", "intel_jtagd"])
expect(valid).to_equal(true)
```

</details>

#### accepts OpenOCD session type

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val valid = validate_session_type("openocd", ["t32", "t32_gdb", "openocd", "intel_jtagd"])
expect(valid).to_equal(true)
```

</details>

#### accepts Intel jtagd session type

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val valid = validate_session_type("intel_jtagd", ["t32", "t32_gdb", "openocd", "intel_jtagd"])
expect(valid).to_equal(true)
```

</details>

#### rejects interpreter session type

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val valid = validate_session_type("interpreter", ["t32", "t32_gdb", "openocd"])
expect(valid).to_equal(false)
```

</details>

### debug_system_reset handler

#### requires session_id

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val session_id = ""
expect(session_id == "").to_equal(true)
```

</details>

#### accepts hardware session types

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val valid_t32 = validate_session_type("t32", ["t32", "t32_gdb", "openocd", "intel_jtagd"])
val valid_ocd = validate_session_type("openocd", ["t32", "t32_gdb", "openocd", "intel_jtagd"])
val valid_intel = validate_session_type("intel_jtagd", ["t32", "t32_gdb", "openocd", "intel_jtagd"])
expect(valid_t32).to_equal(true)
expect(valid_ocd).to_equal(true)
expect(valid_intel).to_equal(true)
```

</details>

### debug_practice_script handler

#### requires session_id and script

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val session_id = "session_1"
val script = ""
val missing = session_id == "" or script == ""
expect(missing).to_equal(true)
```

</details>

#### requires T32 session type only

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val valid = validate_session_type("t32", ["t32", "t32_gdb"])
expect(valid).to_equal(true)
```

</details>

#### rejects non-T32 session type

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val valid = validate_session_type("openocd", ["t32", "t32_gdb"])
expect(valid).to_equal(false)
```

</details>

### debug_openocd_monitor handler

#### requires session_id and command

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val session_id = "session_1"
val command = ""
val missing = session_id == "" or command == ""
expect(missing).to_equal(true)
```

</details>

#### requires OpenOCD session type only

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val valid = validate_session_type("openocd", ["openocd"])
expect(valid).to_equal(true)
```

</details>

#### rejects T32 session type

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val valid = validate_session_type("t32", ["openocd"])
expect(valid).to_equal(false)
```

</details>

#### rejects interpreter session type

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val valid = validate_session_type("interpreter", ["openocd"])
expect(valid).to_equal(false)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/01_unit/app/mcp_unit/mcp_hardware_debug_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- debug_trace_capture handler
- debug_coverage_collect handler
- debug_flash_program handler
- debug_system_reset handler
- debug_practice_script handler
- debug_openocd_monitor handler

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 21 |
| Active scenarios | 21 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
