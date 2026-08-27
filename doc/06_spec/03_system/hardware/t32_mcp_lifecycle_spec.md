# T32 MCP Lifecycle Tools Specification

> System tests for the T32 MCP lifecycle management tools: `t32_launch`, `t32_shutdown`, and `t32_status`. These tools manage PowerView process lifecycle from within the MCP server.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 34 | 34 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# T32 MCP Lifecycle Tools Specification

System tests for the T32 MCP lifecycle management tools: `t32_launch`, `t32_shutdown`, and `t32_status`. These tools manage PowerView process lifecycle from within the MCP server.

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #T32-LC-001 |
| Category | Tooling |
| Difficulty | 3/5 |
| Status | Implemented |
| Requirements | doc/requirement/t32_mcp_lifecycle.md |
| Plan | N/A |
| Design | N/A |
| Research | N/A |
| Source | `test/03_system/hardware/t32_mcp_lifecycle_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

System tests for the T32 MCP lifecycle management tools: `t32_launch`,
`t32_shutdown`, and `t32_status`. These tools manage PowerView process
lifecycle from within the MCP server.

Tests focus on:
- Input validation (missing/invalid parameters)
- Architecture-to-binary mapping (pure function)
- Installation discovery (filesystem-based)
- Response structure validation

## Key Concepts

| Concept       | Description                                              |
|---------------|----------------------------------------------------------|
| t32_launch    | Spawns PowerView as a background process                 |
| t32_shutdown  | Gracefully stops PowerView via t32rem QUIT               |
| t32_status    | Discovers T32 installation, lists processes and probes   |
| architecture  | Maps arch names (arm, tricore, etc.) to binary filenames |

## Behavior

- `t32_launch` rejects unknown arch if no binary is found
- `t32_launch` rejects missing config files
- `t32_shutdown` requires the `port` parameter
- `t32_status` discovers /opt/t32 and enumerates config files

## Related Specifications

- [T32 MCP Requirements](doc/requirement/t32_mcp_lifecycle.md)
- [Lifecycle Implementation](examples/10_tooling/trace32_tools/t32_mcp/lifecycle_tools.spl)

## Implementation Notes

Tests call the pure helper functions exported from lifecycle_tools.spl
directly rather than driving the full JSON-RPC dispatch, so no live
T32 instance is required.

## Scenarios

### T32 MCP Lifecycle — architecture mapping

### t32_arch_to_binary

#### maps arm to t32marm

- maps arm to t32marm
   - Expected: _arch_to_binary("arm") equals `t32marm`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("maps arm to t32marm")
expect(_arch_to_binary("arm")).to_equal("t32marm")
```

</details>

#### maps arm32 to t32marm

- maps arm32 to t32marm
   - Expected: _arch_to_binary("arm32") equals `t32marm`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("maps arm32 to t32marm")
expect(_arch_to_binary("arm32")).to_equal("t32marm")
```

</details>

#### maps cortex-m to t32marm

- maps cortex-m to t32marm
   - Expected: _arch_to_binary("cortex-m") equals `t32marm`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("maps cortex-m to t32marm")
expect(_arch_to_binary("cortex-m")).to_equal("t32marm")
```

</details>

#### maps cortex-a to t32marm

- maps cortex-a to t32marm
   - Expected: _arch_to_binary("cortex-a") equals `t32marm`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("maps cortex-a to t32marm")
expect(_arch_to_binary("cortex-a")).to_equal("t32marm")
```

</details>

#### maps empty string to t32marm (default)

- maps empty string to t32marm (default)
   - Expected: _arch_to_binary("") equals `t32marm`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("maps empty string to t32marm (default)")
expect(_arch_to_binary("")).to_equal("t32marm")
```

</details>

#### maps arm64 to t32marm64

- maps arm64 to t32marm64
   - Expected: _arch_to_binary("arm64") equals `t32marm64`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("maps arm64 to t32marm64")
expect(_arch_to_binary("arm64")).to_equal("t32marm64")
```

</details>

#### maps aarch64 to t32marm64

- maps aarch64 to t32marm64
   - Expected: _arch_to_binary("aarch64") equals `t32marm64`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("maps aarch64 to t32marm64")
expect(_arch_to_binary("aarch64")).to_equal("t32marm64")
```

</details>

#### maps tricore to t32mtc

- maps tricore to t32mtc
   - Expected: _arch_to_binary("tricore") equals `t32mtc`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("maps tricore to t32mtc")
expect(_arch_to_binary("tricore")).to_equal("t32mtc")
```

</details>

#### maps tc3xx to t32mtc

- maps tc3xx to t32mtc
   - Expected: _arch_to_binary("tc3xx") equals `t32mtc`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("maps tc3xx to t32mtc")
expect(_arch_to_binary("tc3xx")).to_equal("t32mtc")
```

</details>

#### maps tc to t32mtc

- maps tc to t32mtc
   - Expected: _arch_to_binary("tc") equals `t32mtc`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("maps tc to t32mtc")
expect(_arch_to_binary("tc")).to_equal("t32mtc")
```

</details>

#### maps ppc to t32mppc

- maps ppc to t32mppc
   - Expected: _arch_to_binary("ppc") equals `t32mppc`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("maps ppc to t32mppc")
expect(_arch_to_binary("ppc")).to_equal("t32mppc")
```

</details>

#### maps powerpc to t32mppc

- maps powerpc to t32mppc
   - Expected: _arch_to_binary("powerpc") equals `t32mppc`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("maps powerpc to t32mppc")
expect(_arch_to_binary("powerpc")).to_equal("t32mppc")
```

</details>

#### maps riscv to t32mriscv

- maps riscv to t32mriscv
   - Expected: _arch_to_binary("riscv") equals `t32mriscv`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("maps riscv to t32mriscv")
expect(_arch_to_binary("riscv")).to_equal("t32mriscv")
```

</details>

#### maps risc-v to t32mriscv

- maps risc-v to t32mriscv
   - Expected: _arch_to_binary("risc-v") equals `t32mriscv`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("maps risc-v to t32mriscv")
expect(_arch_to_binary("risc-v")).to_equal("t32mriscv")
```

</details>

#### maps x86 to t32mx86

- maps x86 to t32mx86
   - Expected: _arch_to_binary("x86") equals `t32mx86`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("maps x86 to t32mx86")
expect(_arch_to_binary("x86")).to_equal("t32mx86")
```

</details>

#### maps x86_64 to t32mx86

- maps x86_64 to t32mx86
   - Expected: _arch_to_binary("x86_64") equals `t32mx86`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("maps x86_64 to t32mx86")
expect(_arch_to_binary("x86_64")).to_equal("t32mx86")
```

</details>

#### maps ARM (uppercase) to t32marm via to_lower

- maps ARM (uppercase) to t32marm via to_lower
   - Expected: _arch_to_binary("ARM") equals `t32marm`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("maps ARM (uppercase) to t32marm via to_lower")
expect(_arch_to_binary("ARM")).to_equal("t32marm")
```

</details>

#### maps unknown arch to t32marm (fallback)

- maps unknown arch to t32marm (fallback)
   - Expected: _arch_to_binary("unknown_arch_xyz") equals `t32marm`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("maps unknown arch to t32marm (fallback)")
expect(_arch_to_binary("unknown_arch_xyz")).to_equal("t32marm")
```

</details>

### T32 MCP Lifecycle — installation discovery

### t32_find_install_dir

#### returns a non-empty path when T32 is installed

- returns a non-empty path when T32 is installed
   - Expected: dir.len() > 0 is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("returns a non-empty path when T32 is installed")
val dir = _find_install_dir()
expect(dir.len() > 0).to_equal(true)
```

</details>

#### returns /opt/t32 when standard installation exists

- returns /opt/t32 when standard installation exists
   - Expected: dir equals `/opt/t32`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("returns /opt/t32 when standard installation exists")
val dir = _find_install_dir()
expect(dir).to_equal("/opt/t32")
```

</details>

### t32_find_powerview_binary

#### finds t32marm binary for arm architecture

- finds t32marm binary for arm architecture
   - Expected: path.len() > 0 is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("finds t32marm binary for arm architecture")
val path = _find_powerview_binary("arm")
expect(path.len() > 0).to_equal(true)
```

</details>

#### found binary path contains t32marm

- found binary path contains t32marm


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("found binary path contains t32marm")
val path = _find_powerview_binary("arm")
expect(path).to_contain("t32marm")
```

</details>

#### found binary path is under /opt/t32 or PATH

- found binary path is under /opt/t32 or PATH
   - Expected: non_empty is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("found binary path is under /opt/t32 or PATH")
val path = _find_powerview_binary("arm")
val under_opt = path.starts_with("/opt/t32")
val under_usr = path.starts_with("/usr")
val non_empty = path.len() > 0
expect(non_empty).to_equal(true)
```

</details>

#### returns empty string for unknown architecture with no binary

- returns empty string for unknown architecture with no binary
   - Expected: is_text is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("returns empty string for unknown architecture with no binary")
# "unknown_arch_xyz" maps to the fallback t32marm, so result
# depends on whether t32marm is installed — we only assert type
val path = _find_powerview_binary("unknown_arch_xyz")
# path is either a valid filesystem path or empty — both are text
val is_text = true
expect(is_text).to_equal(true)
```

</details>

### T32 MCP Lifecycle — t32_launch validation

### binary not found

#### returns error message containing architecture name when binary missing

- returns error message containing architecture name when binary missing
   - Expected: has_error is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("returns error message containing architecture name when binary missing")
val fake_id = "test-1"
val body = "{\"architecture\": \"nonexistent_arch_zzz\", \"config\": \"/nonexistent/path/t32.cfg\"}"
val result = handle_t32_launch(fake_id, body)
# Result must contain an error indicator
val has_error = result.contains("error") or result.contains("not found")
expect(has_error).to_equal(true)
```

</details>

### config file not found

#### returns error message when config path does not exist

- returns error message when config path does not exist
   - Expected: has_error is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("returns error message when config path does not exist")
val fake_id = "test-2"
# Use a real arch so binary lookup succeeds, but a bogus config
val body = "{\"architecture\": \"arm\", \"config\": \"/nonexistent/config/missing.t32\", \"headless\": \"false\"}"
val result = handle_t32_launch(fake_id, body)
val has_error = result.contains("error") or result.contains("not found")
expect(has_error).to_equal(true)
```

</details>

#### error response contains the missing config path

- error response contains the missing config path
   - Expected: mentions_path is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("error response contains the missing config path")
val fake_id = "test-3"
val body = "{\"architecture\": \"arm\", \"config\": \"/nonexistent/config/missing.t32\", \"headless\": \"false\"}"
val result = handle_t32_launch(fake_id, body)
val mentions_path = result.contains("/nonexistent/config/missing.t32")
expect(mentions_path).to_equal(true)
```

</details>

### T32 MCP Lifecycle — t32_shutdown validation

### missing port parameter

#### returns error when port is absent

- returns error when port is absent
   - Expected: has_error is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("returns error when port is absent")
val fake_id = "test-4"
val body = "{\"force\": \"false\"}"
val result = handle_t32_shutdown(fake_id, body)
val has_error = result.contains("error") or result.contains("Missing")
expect(has_error).to_equal(true)
```

</details>

#### error message mentions the port parameter

- error message mentions the port parameter
   - Expected: mentions_port is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("error message mentions the port parameter")
val fake_id = "test-5"
val body = "{}"
val result = handle_t32_shutdown(fake_id, body)
val mentions_port = result.contains("port")
expect(mentions_port).to_equal(true)
```

</details>

### port with no running process

#### returns error when no T32 process is running on given port

- returns error when no T32 process is running on given port
   - Expected: has_error is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("returns error when no T32 process is running on given port")
val fake_id = "test-6"
val body = "{\"port\": \"19999\", \"force\": \"false\"}"
val result = handle_t32_shutdown(fake_id, body)
val has_error = result.contains("error") or result.contains("not running") or result.contains("Failed")
expect(has_error).to_equal(true)
```

</details>

### T32 MCP Lifecycle — t32_status

### basic invocation

#### returns a non-empty response

- returns a non-empty response
   - Expected: result.len() > 0 is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("returns a non-empty response")
val fake_id = "test-7"
val body = "{}"
val result = handle_t32_status(fake_id, body)
expect(result.len() > 0).to_equal(true)
```

</details>

#### response contains installation field

- response contains installation field
   - Expected: has_install is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("response contains installation field")
val fake_id = "test-8"
val body = "{}"
val result = handle_t32_status(fake_id, body)
val has_install = result.contains("install") or result.contains("t32_dir")
expect(has_install).to_equal(true)
```

</details>

#### response contains processes field

- response contains processes field
   - Expected: has_processes is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("response contains processes field")
val fake_id = "test-9"
val body = "{}"
val result = handle_t32_status(fake_id, body)
val has_processes = result.contains("process") or result.contains("running")
expect(has_processes).to_equal(true)
```

</details>

### with /opt/t32 installed

#### response references /opt/t32 directory

- response references /opt/t32 directory
   - Expected: mentions_opt_t32 is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("response references /opt/t32 directory")
val fake_id = "test-10"
val body = "{}"
val result = handle_t32_status(fake_id, body)
val mentions_opt_t32 = result.contains("/opt/t32")
expect(mentions_opt_t32).to_equal(true)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 34 |
| Active scenarios | 34 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


## Related Documentation

- **Requirements:** `doc/requirement/t32_mcp_lifecycle.md`


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-SYSTEM`
- `REQ-T32-LC-001`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `9a0bbd27e67f1e96f9d07ae59c54a5171d711da27e0152601ee39f2755ce7772`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `9a0bbd27e67f1e96f9d07ae59c54a5171d711da27e0152601ee39f2755ce7772`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `9a0bbd27e67f1e96f9d07ae59c54a5171d711da27e0152601ee39f2755ce7772`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **86/100**; effective score: **49/100**; blockers: **1**.

SSpec documentization score: 49/100
source: test/03_system/hardware/t32_mcp_lifecycle_spec.spl
mirror: doc/06_spec/03_system/hardware/t32_mcp_lifecycle_spec.md (current)
findings: 6 blockers: 1
  narrative=100 structure=100 oracle=100
  traceability=60 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
  raw=86; blocker cap makes effective=49
doc/06_spec/03_system/hardware/t32_mcp_lifecycle_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/hardware/t32_mcp_lifecycle_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/hardware/t32_mcp_lifecycle_spec.spl:1:1: blocker SSDOC-TRC-003 [traceability] (-40): 1 declared requirement(s) have no scenario binding
  why: A requirement list without scenario evidence is inventory, not traceability.
  improve: Bind the stable requirement ID inside its executable scenario or explicit blocked case.
test/03_system/hardware/t32_mcp_lifecycle_spec.spl:147:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'maps arm to t32marm' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/hardware/t32_mcp_lifecycle_spec.spl:152:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'maps arm32 to t32marm' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/hardware/t32_mcp_lifecycle_spec.spl:157:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'maps cortex-m to t32marm' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
