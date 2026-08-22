# lifecycle_tools_spec

> Verifies the lifecycle tools behaviour end to end so maintainers of this

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 24 | 24 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# lifecycle_tools_spec

Verifies the lifecycle tools behaviour end to end so maintainers of this

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/01_unit/t32_mcp/lifecycle_tools_spec.spl` |
| Updated | 2026-08-22 |
| Generator | `simple spipe-docgen` (Simple) |

## Purpose and audience
Verifies the lifecycle tools behaviour end to end so maintainers of this
component and reviewers of its spec share one pinned definition.
## Operator workflow
Run `bin/simple test <this spec>`; read the per-scenario verdicts in
the `Results:` summary. Each scenario asserts an observable outcome.
## Compatibility and limitations
Covers the currently shipped behaviour only; performance, stress and
unrelated sibling features are out of scope.

## Scenarios

### t32_arch_to_binary

#### maps arm to t32marm

- Verify: maps arm to t32marm
   - Expected: arch_to_binary("arm") equals `t32marm`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-lifecycle
# @req: REQ-TEST-T32_MCP_LIFECYCLE_TOOLS-001
step("Verify: maps arm to t32marm")
# evidence(expect(...) oracle verified): pinned constants below are authoritative values asserted by this scenario
expect(arch_to_binary("arm")).to_equal("t32marm")
```

</details>

#### maps ARM (uppercase) to t32marm

- Verify: maps ARM (uppercase) to t32marm
   - Expected: arch_to_binary("ARM") equals `t32marm`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-lifecycle
# @req: REQ-TEST-T32_MCP_LIFECYCLE_TOOLS-001
step("Verify: maps ARM (uppercase) to t32marm")
# evidence(expect(...) oracle verified): pinned constants below are authoritative values asserted by this scenario
expect(arch_to_binary("ARM")).to_equal("t32marm")
```

</details>

#### maps arm32 to t32marm

- Verify: maps arm32 to t32marm
   - Expected: arch_to_binary("arm32") equals `t32marm`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-lifecycle
# @req: REQ-TEST-T32_MCP_LIFECYCLE_TOOLS-001
step("Verify: maps arm32 to t32marm")
# evidence(expect(...) oracle verified): pinned constants below are authoritative values asserted by this scenario
expect(arch_to_binary("arm32")).to_equal("t32marm")
```

</details>

#### maps cortex-m to t32marm

- Verify: maps cortex-m to t32marm
   - Expected: arch_to_binary("cortex-m") equals `t32marm`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-lifecycle
# @req: REQ-TEST-T32_MCP_LIFECYCLE_TOOLS-001
step("Verify: maps cortex-m to t32marm")
# evidence(expect(...) oracle verified): pinned constants below are authoritative values asserted by this scenario
expect(arch_to_binary("cortex-m")).to_equal("t32marm")
```

</details>

#### maps cortex-a to t32marm

- Verify: maps cortex-a to t32marm
   - Expected: arch_to_binary("cortex-a") equals `t32marm`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-lifecycle
# @req: REQ-TEST-T32_MCP_LIFECYCLE_TOOLS-001
step("Verify: maps cortex-a to t32marm")
# evidence(expect(...) oracle verified): pinned constants below are authoritative values asserted by this scenario
expect(arch_to_binary("cortex-a")).to_equal("t32marm")
```

</details>

#### maps empty string to default t32marm

- Verify: maps empty string to default t32marm
   - Expected: arch_to_binary("") equals `t32marm`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-lifecycle
# @req: REQ-TEST-T32_MCP_LIFECYCLE_TOOLS-001
step("Verify: maps empty string to default t32marm")
# evidence(expect(...) oracle verified): pinned constants below are authoritative values asserted by this scenario
expect(arch_to_binary("")).to_equal("t32marm")
```

</details>

#### maps arm64 to t32marm64

- Verify: maps arm64 to t32marm64
   - Expected: arch_to_binary("arm64") equals `t32marm64`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-lifecycle
# @req: REQ-TEST-T32_MCP_LIFECYCLE_TOOLS-001
step("Verify: maps arm64 to t32marm64")
# evidence(expect(...) oracle verified): pinned constants below are authoritative values asserted by this scenario
expect(arch_to_binary("arm64")).to_equal("t32marm64")
```

</details>

#### maps aarch64 to t32marm64

- Verify: maps aarch64 to t32marm64
   - Expected: arch_to_binary("aarch64") equals `t32marm64`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-lifecycle
# @req: REQ-TEST-T32_MCP_LIFECYCLE_TOOLS-001
step("Verify: maps aarch64 to t32marm64")
# evidence(expect(...) oracle verified): pinned constants below are authoritative values asserted by this scenario
expect(arch_to_binary("aarch64")).to_equal("t32marm64")
```

</details>

#### maps ARM64 (uppercase) to t32marm64

- Verify: maps ARM64 (uppercase) to t32marm64
   - Expected: arch_to_binary("ARM64") equals `t32marm64`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-lifecycle
# @req: REQ-TEST-T32_MCP_LIFECYCLE_TOOLS-001
step("Verify: maps ARM64 (uppercase) to t32marm64")
# evidence(expect(...) oracle verified): pinned constants below are authoritative values asserted by this scenario
expect(arch_to_binary("ARM64")).to_equal("t32marm64")
```

</details>

#### maps tricore to t32mtc

- Verify: maps tricore to t32mtc
   - Expected: arch_to_binary("tricore") equals `t32mtc`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-lifecycle
# @req: REQ-TEST-T32_MCP_LIFECYCLE_TOOLS-001
step("Verify: maps tricore to t32mtc")
# evidence(expect(...) oracle verified): pinned constants below are authoritative values asserted by this scenario
expect(arch_to_binary("tricore")).to_equal("t32mtc")
```

</details>

#### maps tc3xx to t32mtc

- Verify: maps tc3xx to t32mtc
   - Expected: arch_to_binary("tc3xx") equals `t32mtc`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-lifecycle
# @req: REQ-TEST-T32_MCP_LIFECYCLE_TOOLS-001
step("Verify: maps tc3xx to t32mtc")
# evidence(expect(...) oracle verified): pinned constants below are authoritative values asserted by this scenario
expect(arch_to_binary("tc3xx")).to_equal("t32mtc")
```

</details>

#### maps tc to t32mtc

- Verify: maps tc to t32mtc
   - Expected: arch_to_binary("tc") equals `t32mtc`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-lifecycle
# @req: REQ-TEST-T32_MCP_LIFECYCLE_TOOLS-001
step("Verify: maps tc to t32mtc")
# evidence(expect(...) oracle verified): pinned constants below are authoritative values asserted by this scenario
expect(arch_to_binary("tc")).to_equal("t32mtc")
```

</details>

#### maps ppc to t32mppc

- Verify: maps ppc to t32mppc
   - Expected: arch_to_binary("ppc") equals `t32mppc`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-lifecycle
# @req: REQ-TEST-T32_MCP_LIFECYCLE_TOOLS-001
step("Verify: maps ppc to t32mppc")
# evidence(expect(...) oracle verified): pinned constants below are authoritative values asserted by this scenario
expect(arch_to_binary("ppc")).to_equal("t32mppc")
```

</details>

#### maps powerpc to t32mppc

- Verify: maps powerpc to t32mppc
   - Expected: arch_to_binary("powerpc") equals `t32mppc`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-lifecycle
# @req: REQ-TEST-T32_MCP_LIFECYCLE_TOOLS-001
step("Verify: maps powerpc to t32mppc")
# evidence(expect(...) oracle verified): pinned constants below are authoritative values asserted by this scenario
expect(arch_to_binary("powerpc")).to_equal("t32mppc")
```

</details>

#### maps riscv to t32mriscv

- Verify: maps riscv to t32mriscv
   - Expected: arch_to_binary("riscv") equals `t32mriscv`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-lifecycle
# @req: REQ-TEST-T32_MCP_LIFECYCLE_TOOLS-001
step("Verify: maps riscv to t32mriscv")
# evidence(expect(...) oracle verified): pinned constants below are authoritative values asserted by this scenario
expect(arch_to_binary("riscv")).to_equal("t32mriscv")
```

</details>

#### maps risc-v to t32mriscv

- Verify: maps risc-v to t32mriscv
   - Expected: arch_to_binary("risc-v") equals `t32mriscv`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-lifecycle
# @req: REQ-TEST-T32_MCP_LIFECYCLE_TOOLS-001
step("Verify: maps risc-v to t32mriscv")
# evidence(expect(...) oracle verified): pinned constants below are authoritative values asserted by this scenario
expect(arch_to_binary("risc-v")).to_equal("t32mriscv")
```

</details>

#### maps x86 to t32mx86

- Verify: maps x86 to t32mx86
   - Expected: arch_to_binary("x86") equals `t32mx86`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-lifecycle
# @req: REQ-TEST-T32_MCP_LIFECYCLE_TOOLS-001
step("Verify: maps x86 to t32mx86")
# evidence(expect(...) oracle verified): pinned constants below are authoritative values asserted by this scenario
expect(arch_to_binary("x86")).to_equal("t32mx86")
```

</details>

#### maps x86_64 to t32mx86

- Verify: maps x86_64 to t32mx86
   - Expected: arch_to_binary("x86_64") equals `t32mx86`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-lifecycle
# @req: REQ-TEST-T32_MCP_LIFECYCLE_TOOLS-001
step("Verify: maps x86_64 to t32mx86")
# evidence(expect(...) oracle verified): pinned constants below are authoritative values asserted by this scenario
expect(arch_to_binary("x86_64")).to_equal("t32mx86")
```

</details>

#### maps unknown arch to default t32marm

- Verify: maps unknown arch to default t32marm
   - Expected: arch_to_binary("mips") equals `t32marm`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-lifecycle
# @req: REQ-TEST-T32_MCP_LIFECYCLE_TOOLS-001
step("Verify: maps unknown arch to default t32marm")
# evidence(expect(...) oracle verified): pinned constants below are authoritative values asserted by this scenario
expect(arch_to_binary("mips")).to_equal("t32marm")
```

</details>

### t32_find_install_dir

#### returns configured or standard install dir when present

- Verify: returns configured or standard install dir when present
   - Expected: dir equals `configured`
   - Expected: dir equals `/opt/t32`
   - Expected: dir equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-lifecycle
# @req: REQ-TEST-T32_MCP_LIFECYCLE_TOOLS-001
step("Verify: returns configured or standard install dir when present")
# evidence(expect(...) oracle verified): pinned constants below are authoritative values asserted by this scenario
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

- Verify: returns a stable result across repeated lookup
   - Expected: find_install_dir() equals `dir`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-lifecycle
# @req: REQ-TEST-T32_MCP_LIFECYCLE_TOOLS-001
step("Verify: returns a stable result across repeated lookup")
# evidence(expect(...) oracle verified): pinned constants below are authoritative values asserted by this scenario
val dir = find_install_dir()
expect(find_install_dir()).to_equal(dir)
```

</details>

### t32_check_xvfb

#### matches xvfb-run availability on the current host

- Verify: matches xvfb-run availability on the current host
   - Expected: result is true
   - Expected: result is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-lifecycle
# @req: REQ-TEST-T32_MCP_LIFECYCLE_TOOLS-001
step("Verify: matches xvfb-run availability on the current host")
# evidence(expect(...) oracle verified): pinned constants below are authoritative values asserted by this scenario
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

- Verify: returns false when no service is listening on an unused port
   - Expected: result is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-lifecycle
# @req: REQ-TEST-T32_MCP_LIFECYCLE_TOOLS-001
step("Verify: returns false when no service is listening on an unused port")
# evidence(expect(...) oracle verified): pinned constants below are authoritative values asserted by this scenario
# Port 19999 should not have a T32 instance running
val result = ping_port("t32rem64", 19999)
expect(result).to_equal(false)
```

</details>

#### returns false for an invalid backend on a closed port

- Verify: returns false for an invalid backend on a closed port
   - Expected: result is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-lifecycle
# @req: REQ-TEST-T32_MCP_LIFECYCLE_TOOLS-001
step("Verify: returns false for an invalid backend on a closed port")
# evidence(expect(...) oracle verified): pinned constants below are authoritative values asserted by this scenario
val result = ping_port("t32rem64", 65000)
expect(result).to_equal(false)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 24 |
| Active scenarios | 24 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `3a23bc3fd1afaf6a073bc6f0d50f8a033e7a55c582a609a2d16cfd71b057f576`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `3a23bc3fd1afaf6a073bc6f0d50f8a033e7a55c582a609a2d16cfd71b057f576`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `3a23bc3fd1afaf6a073bc6f0d50f8a033e7a55c582a609a2d16cfd71b057f576`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **94/100**; effective score: **94/100**; blockers: **0**.

SSpec documentization score: 94/100
source: test/01_unit/t32_mcp/lifecycle_tools_spec.spl
mirror: doc/06_spec/01_unit/t32_mcp/lifecycle_tools_spec.md (current)
findings: 3 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=85 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/t32_mcp/lifecycle_tools_spec.md:1:1: warning SSDOC-EVD-002 [evidence] (-15): source steps are not visible in the generated manual
  why: Source tokens alone do not prove reader-visible workflow structure.
  improve: Use supported literal step calls and regenerate the manual.
doc/06_spec/01_unit/t32_mcp/lifecycle_tools_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/t32_mcp/lifecycle_tools_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: assumptions/preconditions, traceability, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
<!-- sspec-maintain:scorecard:end -->
