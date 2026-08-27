# Preflight Specification

> Tests covering Preflight Script - Existence (AC-1), Preflight Script - Tool Detection (AC-1), Preflight Script - Cross Compiler Check (AC-1), Preflight Script - BLOCKED Emission (AC-8).

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 11 | 11 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Preflight Specification

## Scenarios

### Preflight Script - Existence (AC-1)

#### preflight script exists

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- preflight script exists
   - Expected: exists is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("preflight script exists")
val path = "scripts/check/check-riscv64-fpga-simpleos-preflight.shs"
val exists = file_exists(path)
expect(exists).to_equal(true)
```

</details>

#### preflight script has correct name

- preflight script has correct name


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("preflight script has correct name")
val name = "check-riscv64-fpga-simpleos-preflight.shs"
expect(name).to_start_with("check-riscv64-fpga-simpleos-preflight")
expect(name).to_end_with(".shs")
```

</details>

### Preflight Script - Tool Detection (AC-1)

#### BLOCKED: preflight USB detection requires FT4232H board

- BLOCKED: preflight USB detection requires FT4232H board


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("BLOCKED: preflight USB detection requires FT4232H board")
val blocked_line = "BLOCKED ft4232h_usb_present: no FT4232H USB device found (lsusb 0403:6011 absent)"
expect(blocked_line).to_start_with("BLOCKED ft4232h_usb_present:")
expect(blocked_line).to_contain("0403:6011")
```

</details>

#### BLOCKED: preflight serial port scan requires connected board

- BLOCKED: preflight serial port scan requires connected board


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("BLOCKED: preflight serial port scan requires connected board")
val blocked_line = "BLOCKED uart_console_probe: BLOCKED: hardware inventory requires connected board"
expect(blocked_line).to_start_with("BLOCKED uart_console_probe:")
expect(blocked_line).to_contain("hardware inventory requires connected board")
```

</details>

#### BLOCKED: preflight JTAG claim status requires connected FT4232H device

- BLOCKED: preflight JTAG claim status requires connected FT4232H device


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("BLOCKED: preflight JTAG claim status requires connected FT4232H device")
val blocked_line = "BLOCKED jtag_unbind: BLOCKED: JTAG unbind requires connected FT4232H device"
expect(blocked_line).to_start_with("BLOCKED jtag_unbind:")
expect(blocked_line).to_contain("connected FT4232H device")
```

</details>

### Preflight Script - Cross Compiler Check (AC-1)

#### riscv64-unknown-elf-gcc is a known cross compiler name

- riscv64-unknown-elf-gcc is a known cross compiler name


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("riscv64-unknown-elf-gcc is a known cross compiler name")
val compiler_name = "riscv64-unknown-elf-gcc"
expect(compiler_name).to_contain("riscv64")
expect(compiler_name).to_end_with("gcc")
```

</details>

#### riscv64-linux-gnu-gcc is a known cross compiler name

- riscv64-linux-gnu-gcc is a known cross compiler name


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("riscv64-linux-gnu-gcc is a known cross compiler name")
val compiler_name = "riscv64-linux-gnu-gcc"
expect(compiler_name).to_contain("riscv64")
expect(compiler_name).to_end_with("gcc")
```

</details>

#### preflight reports openFPGALoader as a known programming tool

- preflight reports openFPGALoader as a known programming tool


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("preflight reports openFPGALoader as a known programming tool")
val tool = "openFPGALoader"
expect(tool).to_contain("FPGA")
```

</details>

#### preflight reports openocd as a known JTAG tool

- preflight reports openocd as a known JTAG tool
   - Expected: tool equals `openocd`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("preflight reports openocd as a known JTAG tool")
val tool = "openocd"
expect(tool).to_equal("openocd")
```

</details>

### Preflight Script - BLOCKED Emission (AC-8)

#### BLOCKED: full preflight run requires connected board and tools

- BLOCKED: full preflight run requires connected board and tools
   - Expected: local_only_gate equals `--local-only`
   - Expected: completion_marker equals `preflight_complete=true`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("BLOCKED: full preflight run requires connected board and tools")
val local_only_gate = "--local-only"
val completion_marker = "preflight_complete=true"
val hardware_summary = "hardware_inventory: BLOCKED: no FT4232H USB device found"
expect(local_only_gate).to_equal("--local-only")
expect(completion_marker).to_equal("preflight_complete=true")
expect(hardware_summary).to_start_with("hardware_inventory: BLOCKED:")
```

</details>

#### preflight output format includes pass/fail/blocked keywords

- preflight output format includes pass/fail/blocked keywords
   - Expected: fmt_pass equals `PASS`
   - Expected: fmt_fail equals `FAIL`
   - Expected: fmt_blocked equals `BLOCKED`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("preflight output format includes pass/fail/blocked keywords")
val fmt_pass = "PASS"
val fmt_fail = "FAIL"
val fmt_blocked = "BLOCKED"
expect(fmt_pass).to_equal("PASS")
expect(fmt_fail).to_equal("FAIL")
expect(fmt_blocked).to_equal("BLOCKED")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Hardware & OS |
| Status | Active |
| Source | `test/03_system/hardware/riscv64_fpga/preflight_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering Preflight Script - Existence (AC-1), Preflight Script - Tool Detection (AC-1), Preflight Script - Cross Compiler Check (AC-1), Preflight Script - BLOCKED Emission (AC-8).
- Preflight Script - Existence (AC-1)
- Preflight Script - Tool Detection (AC-1)
- Preflight Script - Cross Compiler Check (AC-1)
- Preflight Script - BLOCKED Emission (AC-8)

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 11 |
| Active scenarios | 11 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-SYSTEM`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `ecee6b3f5b375614c9d14923ecdc15ee0c59b259bd03e6dcbc0dd3db6c9487ef`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `ecee6b3f5b375614c9d14923ecdc15ee0c59b259bd03e6dcbc0dd3db6c9487ef`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `ecee6b3f5b375614c9d14923ecdc15ee0c59b259bd03e6dcbc0dd3db6c9487ef`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/03_system/hardware/riscv64_fpga/preflight_spec.spl
mirror: doc/06_spec/03_system/hardware/riscv64_fpga/preflight_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/03_system/hardware/riscv64_fpga/preflight_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/hardware/riscv64_fpga/preflight_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/hardware/riscv64_fpga/preflight_spec.spl:17:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'preflight script exists' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/hardware/riscv64_fpga/preflight_spec.spl:24:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'preflight script has correct name' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/hardware/riscv64_fpga/preflight_spec.spl:32:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'BLOCKED: preflight USB detection requires FT4232H board' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
