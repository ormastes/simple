# Vhdl Vendor Synthesis Smoke Specification

> <details>

<!-- sdn-diagram:id=vhdl_vendor_synthesis_smoke_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=vhdl_vendor_synthesis_smoke_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

vhdl_vendor_synthesis_smoke_spec -> std
vhdl_vendor_synthesis_smoke_spec -> ieee
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=vhdl_vendor_synthesis_smoke_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 5 | 5 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Vhdl Vendor Synthesis Smoke Specification

## Scenarios

### VHDL vendor synthesis smoke

#### skips clearly when vendor smoke is disabled

<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(selected_vendor_tool("vivado")).to_equal("vivado")
expect(selected_vendor_tool("quartus")).to_equal("quartus_sh")
expect(selected_vendor_tool("yosys")).to_equal("yosys")
expect(selected_vendor_tool("")).to_equal("ghdl")
expect(selected_vendor_tool("unknown")).to_equal("ghdl")
```

</details>

#### reports deterministic vendor smoke output paths and command

<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

<details>
<summary>Executable SSpec</summary>

Runnable source: 17 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

<details>
<summary>Executable SSpec</summary>

Runnable source: 27 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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
| Source | `test/01_unit/compiler/backend/vhdl_vendor_synthesis_smoke_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
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
