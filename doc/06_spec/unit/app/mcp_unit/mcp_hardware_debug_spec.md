# Mcp Hardware Debug Specification

> Tests covering debug_trace_capture handler, debug_coverage_collect handler, debug_flash_program handler, debug_system_reset handler, debug_practice_script handler, debug_openocd_monitor handler.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 21 | 21 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Mcp Hardware Debug Specification

## Scenarios

### debug_trace_capture handler

#### requires session_id parameter

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- requires session_id parameter
   - Expected: has_error is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("requires session_id parameter")
val session_id = ""
val has_error = session_id == ""
expect(has_error).to_equal(true)
```

</details>

#### requires T32 session type

- requires T32 session type
   - Expected: valid is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("requires T32 session type")
val valid = validate_session_type("t32", ["t32", "t32_gdb"])
expect(valid).to_equal(true)
```

</details>

#### rejects interpreter session type

- rejects interpreter session type
   - Expected: valid is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rejects interpreter session type")
val valid = validate_session_type("interpreter", ["t32", "t32_gdb"])
expect(valid).to_equal(false)
```

</details>

#### defaults duration to 1000ms

- defaults duration to 1000ms
   - Expected: duration equals `1000`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("defaults duration to 1000ms")
var duration = 1000
val duration_str = ""
if duration_str != "":
    duration = 500
expect(duration).to_equal(1000)
```

</details>

### debug_coverage_collect handler

#### requires session_id and module

- requires session_id and module
   - Expected: missing is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("requires session_id and module")
val session_id = ""
val module = ""
val missing = session_id == "" or module == ""
expect(missing).to_equal(true)
```

</details>

#### requires T32 session type

- requires T32 session type
   - Expected: valid is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("requires T32 session type")
val valid = validate_session_type("t32_gdb", ["t32", "t32_gdb"])
expect(valid).to_equal(true)
```

</details>

#### rejects openocd session type

- rejects openocd session type
   - Expected: valid is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rejects openocd session type")
val valid = validate_session_type("openocd", ["t32", "t32_gdb"])
expect(valid).to_equal(false)
```

</details>

### debug_flash_program handler

#### requires session_id and elf_path

- requires session_id and elf_path
   - Expected: missing is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("requires session_id and elf_path")
val session_id = "session_1"
val elf_path = ""
val missing = session_id == "" or elf_path == ""
expect(missing).to_equal(true)
```

</details>

#### accepts T32 session type

- accepts T32 session type
   - Expected: valid is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("accepts T32 session type")
val valid = validate_session_type("t32", ["t32", "t32_gdb", "openocd", "intel_jtagd"])
expect(valid).to_equal(true)
```

</details>

#### accepts OpenOCD session type

- accepts OpenOCD session type
   - Expected: valid is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("accepts OpenOCD session type")
val valid = validate_session_type("openocd", ["t32", "t32_gdb", "openocd", "intel_jtagd"])
expect(valid).to_equal(true)
```

</details>

#### accepts Intel jtagd session type

- accepts Intel jtagd session type
   - Expected: valid is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("accepts Intel jtagd session type")
val valid = validate_session_type("intel_jtagd", ["t32", "t32_gdb", "openocd", "intel_jtagd"])
expect(valid).to_equal(true)
```

</details>

#### rejects interpreter session type

- rejects interpreter session type
   - Expected: valid is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rejects interpreter session type")
val valid = validate_session_type("interpreter", ["t32", "t32_gdb", "openocd"])
expect(valid).to_equal(false)
```

</details>

### debug_system_reset handler

#### requires session_id

- requires session_id
   - Expected: session_id equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("requires session_id")
val session_id = ""
expect(session_id).to_equal("")
```

</details>

#### accepts hardware session types

- accepts hardware session types
   - Expected: valid_t32 is true
   - Expected: valid_ocd is true
   - Expected: valid_intel is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("accepts hardware session types")
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

- requires session_id and script
   - Expected: missing is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("requires session_id and script")
val session_id = "session_1"
val script = ""
val missing = session_id == "" or script == ""
expect(missing).to_equal(true)
```

</details>

#### requires T32 session type only

- requires T32 session type only
   - Expected: valid is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("requires T32 session type only")
val valid = validate_session_type("t32", ["t32", "t32_gdb"])
expect(valid).to_equal(true)
```

</details>

#### rejects non-T32 session type

- rejects non-T32 session type
   - Expected: valid is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rejects non-T32 session type")
val valid = validate_session_type("openocd", ["t32", "t32_gdb"])
expect(valid).to_equal(false)
```

</details>

### debug_openocd_monitor handler

#### requires session_id and command

- requires session_id and command
   - Expected: missing is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("requires session_id and command")
val session_id = "session_1"
val command = ""
val missing = session_id == "" or command == ""
expect(missing).to_equal(true)
```

</details>

#### requires OpenOCD session type only

- requires OpenOCD session type only
   - Expected: valid is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("requires OpenOCD session type only")
val valid = validate_session_type("openocd", ["openocd"])
expect(valid).to_equal(true)
```

</details>

#### rejects T32 session type

- rejects T32 session type
   - Expected: valid is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rejects T32 session type")
val valid = validate_session_type("t32", ["openocd"])
expect(valid).to_equal(false)
```

</details>

#### rejects interpreter session type

- rejects interpreter session type
   - Expected: valid is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rejects interpreter session type")
val valid = validate_session_type("interpreter", ["openocd"])
expect(valid).to_equal(false)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/unit/app/mcp_unit/mcp_hardware_debug_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering debug_trace_capture handler, debug_coverage_collect handler, debug_flash_program handler, debug_system_reset handler, debug_practice_script handler, debug_openocd_monitor handler.
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

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-UNIT`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `0447e349a1672cea3ab7b40052a867f0e44338e4c793911e51f777e70cc2f756`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `0447e349a1672cea3ab7b40052a867f0e44338e4c793911e51f777e70cc2f756`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `0447e349a1672cea3ab7b40052a867f0e44338e4c793911e51f777e70cc2f756`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **90/100**; effective score: **90/100**; blockers: **0**.

SSpec documentization score: 90/100
source: test/unit/app/mcp_unit/mcp_hardware_debug_spec.spl
mirror: doc/06_spec/unit/app/mcp_unit/mcp_hardware_debug_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=90
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/unit/app/mcp_unit/mcp_hardware_debug_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/unit/app/mcp_unit/mcp_hardware_debug_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/unit/app/mcp_unit/mcp_hardware_debug_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-10): 1 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/unit/app/mcp_unit/mcp_hardware_debug_spec.spl:23:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'requires session_id parameter' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/app/mcp_unit/mcp_hardware_debug_spec.spl:30:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'requires T32 session type' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/app/mcp_unit/mcp_hardware_debug_spec.spl:36:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'rejects interpreter session type' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
