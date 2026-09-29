# Lifecycle Tools Specification

> Tests covering t32_arch_to_binary, t32_find_install_dir, t32_check_xvfb, t32_ping_port.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 24 | 24 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Lifecycle Tools Specification

## Scenarios

### t32_arch_to_binary

#### maps arm to t32marm

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- maps arm to t32marm
   - Expected: arch_to_binary("arm") equals `t32marm`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-T32_MCP
step("maps arm to t32marm")
expect(arch_to_binary("arm")).to_equal("t32marm")
```

</details>

#### maps ARM (uppercase) to t32marm

- maps ARM (uppercase) to t32marm
   - Expected: arch_to_binary("ARM") equals `t32marm`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-T32_MCP
step("maps ARM (uppercase) to t32marm")
expect(arch_to_binary("ARM")).to_equal("t32marm")
```

</details>

#### maps arm32 to t32marm

- maps arm32 to t32marm
   - Expected: arch_to_binary("arm32") equals `t32marm`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-T32_MCP
step("maps arm32 to t32marm")
expect(arch_to_binary("arm32")).to_equal("t32marm")
```

</details>

#### maps cortex-m to t32marm

- maps cortex-m to t32marm
   - Expected: arch_to_binary("cortex-m") equals `t32marm`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-T32_MCP
step("maps cortex-m to t32marm")
expect(arch_to_binary("cortex-m")).to_equal("t32marm")
```

</details>

#### maps cortex-a to t32marm

- maps cortex-a to t32marm
   - Expected: arch_to_binary("cortex-a") equals `t32marm`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-T32_MCP
step("maps cortex-a to t32marm")
expect(arch_to_binary("cortex-a")).to_equal("t32marm")
```

</details>

#### maps empty string to default t32marm

- maps empty string to default t32marm
   - Expected: arch_to_binary("") equals `t32marm`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-T32_MCP
step("maps empty string to default t32marm")
expect(arch_to_binary("")).to_equal("t32marm")
```

</details>

#### maps arm64 to t32marm64

- maps arm64 to t32marm64
   - Expected: arch_to_binary("arm64") equals `t32marm64`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-T32_MCP
step("maps arm64 to t32marm64")
expect(arch_to_binary("arm64")).to_equal("t32marm64")
```

</details>

#### maps aarch64 to t32marm64

- maps aarch64 to t32marm64
   - Expected: arch_to_binary("aarch64") equals `t32marm64`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-T32_MCP
step("maps aarch64 to t32marm64")
expect(arch_to_binary("aarch64")).to_equal("t32marm64")
```

</details>

#### maps ARM64 (uppercase) to t32marm64

- maps ARM64 (uppercase) to t32marm64
   - Expected: arch_to_binary("ARM64") equals `t32marm64`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-T32_MCP
step("maps ARM64 (uppercase) to t32marm64")
expect(arch_to_binary("ARM64")).to_equal("t32marm64")
```

</details>

#### maps tricore to t32mtc

- maps tricore to t32mtc
   - Expected: arch_to_binary("tricore") equals `t32mtc`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-T32_MCP
step("maps tricore to t32mtc")
expect(arch_to_binary("tricore")).to_equal("t32mtc")
```

</details>

#### maps tc3xx to t32mtc

- maps tc3xx to t32mtc
   - Expected: arch_to_binary("tc3xx") equals `t32mtc`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-T32_MCP
step("maps tc3xx to t32mtc")
expect(arch_to_binary("tc3xx")).to_equal("t32mtc")
```

</details>

#### maps tc to t32mtc

- maps tc to t32mtc
   - Expected: arch_to_binary("tc") equals `t32mtc`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-T32_MCP
step("maps tc to t32mtc")
expect(arch_to_binary("tc")).to_equal("t32mtc")
```

</details>

#### maps ppc to t32mppc

- maps ppc to t32mppc
   - Expected: arch_to_binary("ppc") equals `t32mppc`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-T32_MCP
step("maps ppc to t32mppc")
expect(arch_to_binary("ppc")).to_equal("t32mppc")
```

</details>

#### maps powerpc to t32mppc

- maps powerpc to t32mppc
   - Expected: arch_to_binary("powerpc") equals `t32mppc`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-T32_MCP
step("maps powerpc to t32mppc")
expect(arch_to_binary("powerpc")).to_equal("t32mppc")
```

</details>

#### maps riscv to t32mriscv

- maps riscv to t32mriscv
   - Expected: arch_to_binary("riscv") equals `t32mriscv`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-T32_MCP
step("maps riscv to t32mriscv")
expect(arch_to_binary("riscv")).to_equal("t32mriscv")
```

</details>

#### maps risc-v to t32mriscv

- maps risc-v to t32mriscv
   - Expected: arch_to_binary("risc-v") equals `t32mriscv`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-T32_MCP
step("maps risc-v to t32mriscv")
expect(arch_to_binary("risc-v")).to_equal("t32mriscv")
```

</details>

#### maps x86 to t32mx86

- maps x86 to t32mx86
   - Expected: arch_to_binary("x86") equals `t32mx86`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-T32_MCP
step("maps x86 to t32mx86")
expect(arch_to_binary("x86")).to_equal("t32mx86")
```

</details>

#### maps x86_64 to t32mx86

- maps x86_64 to t32mx86
   - Expected: arch_to_binary("x86_64") equals `t32mx86`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-T32_MCP
step("maps x86_64 to t32mx86")
expect(arch_to_binary("x86_64")).to_equal("t32mx86")
```

</details>

#### maps unknown arch to default t32marm

- maps unknown arch to default t32marm
   - Expected: arch_to_binary("mips") equals `t32marm`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-T32_MCP
step("maps unknown arch to default t32marm")
expect(arch_to_binary("mips")).to_equal("t32marm")
```

</details>

### t32_find_install_dir

#### returns configured or standard install dir when present

- returns configured or standard install dir when present
   - Expected: dir equals `configured`
   - Expected: dir equals `/opt/t32`
   - Expected: dir equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-T32_MCP
step("returns configured or standard install dir when present")
val dir = find_install_dir()
val configured = env_get("T32MEM")
if configured != "":
    expect(dir).to_equal(configured)
elif file_exists("/opt/t32"):
    expect(dir).to_equal("/opt/t32")
else:
    expect(dir).to_equal("")
```

</details>

#### returns a stable result across repeated lookup

- returns a stable result across repeated lookup
   - Expected: find_install_dir() equals `dir`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-T32_MCP
step("returns a stable result across repeated lookup")
val dir = find_install_dir()
expect(find_install_dir()).to_equal(dir)
```

</details>

### t32_check_xvfb

#### matches xvfb-run availability on the current host

- matches xvfb-run availability on the current host
   - Expected: result is true
   - Expected: result is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-T32_MCP
step("matches xvfb-run availability on the current host")
val result = check_xvfb()
val (_stdout, _stderr, rc) = process_run("/bin/sh", ["-c", "which xvfb-run 2>/dev/null"])
if rc == 0:
    expect(result).to_equal(true)
else:
    expect(result).to_equal(false)
```

</details>

### t32_ping_port

#### returns false when no service is listening on an unused port

- returns false when no service is listening on an unused port
   - Expected: result is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-T32_MCP
step("returns false when no service is listening on an unused port")
# Port 19999 should not have a T32 instance running
val result = ping_port("t32rem64", 19999)
expect(result).to_equal(false)
```

</details>

#### returns false for an invalid backend on a closed port

- returns false for an invalid backend on a closed port
   - Expected: result is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-T32_MCP
step("returns false for an invalid backend on a closed port")
val result = ping_port("t32rem64", 65000)
expect(result).to_equal(false)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/01_unit/t32_mcp/lifecycle_tools_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering t32_arch_to_binary, t32_find_install_dir, t32_check_xvfb, t32_ping_port.
- t32_arch_to_binary
- t32_find_install_dir
- t32_check_xvfb
- t32_ping_port

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 24 |
| Active scenarios | 24 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-UNIT`
- `REQ-lifecycle`
- `REQ-SSPEC-T32_MCP`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `81a99230382b770951d437ed0132f8f4732f3c60d35e5eaea68036886d57e5d4`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `81a99230382b770951d437ed0132f8f4732f3c60d35e5eaea68036886d57e5d4`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `81a99230382b770951d437ed0132f8f4732f3c60d35e5eaea68036886d57e5d4`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **86/100**; effective score: **49/100**; blockers: **1**.

SSpec documentization score: 49/100
source: test/01_unit/t32_mcp/lifecycle_tools_spec.spl
mirror: doc/06_spec/01_unit/t32_mcp/lifecycle_tools_spec.md (current)
findings: 6 blockers: 1
  narrative=100 structure=100 oracle=100
  traceability=60 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
  raw=86; blocker cap makes effective=49
doc/06_spec/01_unit/t32_mcp/lifecycle_tools_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/t32_mcp/lifecycle_tools_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/t32_mcp/lifecycle_tools_spec.spl:1:1: blocker SSDOC-TRC-003 [traceability] (-40): 2 declared requirement(s) have no scenario binding
  why: A requirement list without scenario evidence is inventory, not traceability.
  improve: Bind the stable requirement ID inside its executable scenario or explicit blocked case.
test/01_unit/t32_mcp/lifecycle_tools_spec.spl:68:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'maps arm to t32marm' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/t32_mcp/lifecycle_tools_spec.spl:73:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'maps ARM (uppercase) to t32marm' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/t32_mcp/lifecycle_tools_spec.spl:78:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'maps arm32 to t32marm' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
