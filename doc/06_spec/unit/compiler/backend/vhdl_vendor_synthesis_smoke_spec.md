# Vhdl Vendor Synthesis Smoke Specification

> Tests covering VHDL vendor synthesis smoke.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 5 | 5 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Vhdl Vendor Synthesis Smoke Specification

## Scenarios

### VHDL vendor synthesis smoke

#### skips clearly when vendor smoke is disabled

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- skips clearly when vendor smoke is disabled
   - Expected: vendor_smoke_enabled() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("skips clearly when vendor smoke is disabled")
val vendor = selected_vendor()
val tool = selected_vendor_tool(vendor)
val report_path = vendor_smoke_report_path(vendor)
val log_path = vendor_smoke_log_path(vendor)
if not vendor_smoke_enabled():
    val diagnostic = disabled_diagnostic(vendor, tool, report_path, log_path)
    print diagnostic
    expect(diagnostic).to_contain("SIMPLE_VHDL_VENDOR_SMOKE is not 1")
    expect(diagnostic).to_contain("status=disabled")
    expect(report_path).to_contain("build/vhdl/vendor-smoke/")
    expect(log_path).to_contain("build/vhdl/vendor-smoke/")
else:
    expect(vendor_smoke_enabled()).to_equal(true)
```

</details>

#### maps supported vendor names to executable tools

- maps supported vendor names to executable tools
   - Expected: selected_vendor_tool("vivado") equals `vivado`
   - Expected: selected_vendor_tool("quartus") equals `quartus_sh`
   - Expected: selected_vendor_tool("yosys") equals `yosys`
   - Expected: selected_vendor_tool("") equals `ghdl`
   - Expected: selected_vendor_tool("unknown") equals `ghdl`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("maps supported vendor names to executable tools")
expect(selected_vendor_tool("vivado")).to_equal("vivado")
expect(selected_vendor_tool("quartus")).to_equal("quartus_sh")
expect(selected_vendor_tool("yosys")).to_equal("yosys")
expect(selected_vendor_tool("")).to_equal("ghdl")
expect(selected_vendor_tool("unknown")).to_equal("ghdl")
```

</details>

#### reports deterministic vendor smoke output paths and command

- reports deterministic vendor smoke output paths and command


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("reports deterministic vendor smoke output paths and command")
val vendor = selected_vendor()
val tool = selected_vendor_tool(vendor)
val vhdl_path = vendor_smoke_vhdl_path(vendor)
val report_path = vendor_smoke_report_path(vendor)
val log_path = vendor_smoke_log_path(vendor)
val command_line = vendor_smoke_command_line(vendor, tool, vhdl_path)
val diagnostic = ready_diagnostic(vendor, tool, report_path, log_path)
expect(report_path).to_contain("-report.sdn")
expect(log_path).to_contain(".log")
expect(diagnostic).to_contain("report_path=")
expect(diagnostic).to_contain("log_path=")
expect(command_line).to_contain(tool)
expect(command_line).to_contain(vhdl_path)
```

</details>

#### skips clearly when the selected vendor tool is missing

- skips clearly when the selected vendor tool is missing
   - Expected: available is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 19 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("skips clearly when the selected vendor tool is missing")
val vendor = selected_vendor()
val tool = selected_vendor_tool(vendor)
val report_path = vendor_smoke_report_path(vendor)
val log_path = vendor_smoke_log_path(vendor)
val available = tool_available(tool)
if not vendor_smoke_enabled():
    val diagnostic = disabled_diagnostic(vendor, tool, report_path, log_path)
    print diagnostic
    expect(diagnostic).to_contain("status=disabled")
else:
    if available:
        expect(available).to_equal(true)
    else:
        val diagnostic = missing_tool_diagnostic(vendor, tool, report_path, log_path)
        print diagnostic
        expect(diagnostic).to_contain("status=missing-tool")
        expect(diagnostic).to_contain(tool)
```

</details>

#### captures command report and log when vendor smoke is enabled

- captures command report and log when vendor smoke is enabled
   - Expected: code equals `0`
   - Expected: shell_file_exists(report_path) is true
   - Expected: shell_file_exists(log_path) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 29 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("captures command report and log when vendor smoke is enabled")
val vendor = selected_vendor()
val tool = selected_vendor_tool(vendor)
val vhdl_path = vendor_smoke_vhdl_path(vendor)
val report_path = vendor_smoke_report_path(vendor)
val log_path = vendor_smoke_log_path(vendor)
val command_line = vendor_smoke_command_line(vendor, tool, vhdl_path)
val available = tool_available(tool)
if not vendor_smoke_enabled():
    val diagnostic = disabled_diagnostic(vendor, tool, report_path, log_path)
    print diagnostic
    expect(diagnostic).to_contain("status=disabled")
else:
    if available:
        val code = run_vendor_smoke(vendor, tool, vhdl_path, report_path, log_path, command_line)
        val diagnostic = "DONE: status=executed; vendor=" + vendor + "; tool=" + tool + "; exit_code={code}; report_path=" + report_path + "; log_path=" + log_path
        print diagnostic
        expect(code).to_equal(0)
        expect(shell_file_exists(report_path)).to_equal(true)
        expect(shell_file_exists(log_path)).to_equal(true)
        expect(shell_read_text(report_path)).to_contain("command: " + command_line)
        expect(shell_read_text(report_path)).to_contain("exit_code: 0")
        expect(shell_read_text(log_path)).to_contain("stdout:")
        expect(shell_read_text(log_path)).to_contain("stderr:")
    else:
        val diagnostic = missing_tool_diagnostic(vendor, tool, report_path, log_path)
        print diagnostic
        expect(diagnostic).to_contain("status=missing-tool")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/unit/compiler/backend/vhdl_vendor_synthesis_smoke_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering VHDL vendor synthesis smoke.
- VHDL vendor synthesis smoke

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 5 |
| Active scenarios | 5 |
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

- Canonical SPipe generation for source `00983e2dc7dbb290a70ff723ca3c4d6a951c7964c747fb91084fb1c08889e711`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `00983e2dc7dbb290a70ff723ca3c4d6a951c7964c747fb91084fb1c08889e711`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `00983e2dc7dbb290a70ff723ca3c4d6a951c7964c747fb91084fb1c08889e711`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **90/100**; effective score: **90/100**; blockers: **0**.

SSpec documentization score: 90/100
source: test/unit/compiler/backend/vhdl_vendor_synthesis_smoke_spec.spl
mirror: doc/06_spec/unit/compiler/backend/vhdl_vendor_synthesis_smoke_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=90
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/unit/compiler/backend/vhdl_vendor_synthesis_smoke_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/unit/compiler/backend/vhdl_vendor_synthesis_smoke_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/unit/compiler/backend/vhdl_vendor_synthesis_smoke_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-10): 1 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/unit/compiler/backend/vhdl_vendor_synthesis_smoke_spec.spl:133:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'skips clearly when vendor smoke is disabled' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/compiler/backend/vhdl_vendor_synthesis_smoke_spec.spl:150:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'maps supported vendor names to executable tools' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/compiler/backend/vhdl_vendor_synthesis_smoke_spec.spl:159:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'reports deterministic vendor smoke output paths and command' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
