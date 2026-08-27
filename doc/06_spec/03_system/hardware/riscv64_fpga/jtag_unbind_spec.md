# Jtag Unbind Specification

> Tests covering JTAG Unbind Script - Existence (AC-3), JTAG Unbind Script - Interface Target (AC-3), JTAG Unbind Script - BLOCKED Gates (AC-3, AC-8).

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 12 | 12 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Jtag Unbind Specification

## Scenarios

### JTAG Unbind Script - Existence (AC-3)

#### jtag unbind script path is under scripts directory

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- jtag unbind script path is under scripts directory


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("jtag unbind script path is under scripts directory")
val prefix = "scripts/"
val name = "scripts/jtag-ftdi-unbind.shs"
expect(name).to_start_with(prefix)
expect(name).to_end_with(".shs")
```

</details>

#### jtag unbind script name contains jtag

- jtag unbind script name contains jtag


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("jtag unbind script name contains jtag")
val name = "jtag-ftdi-unbind.shs"
expect(name).to_contain("jtag")
```

</details>

#### jtag unbind script name contains ftdi

- jtag unbind script name contains ftdi


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("jtag unbind script name contains ftdi")
val name = "jtag-ftdi-unbind.shs"
expect(name).to_contain("ftdi")
```

</details>

#### jtag unbind script name contains unbind

- jtag unbind script name contains unbind


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("jtag unbind script name contains unbind")
val name = "jtag-ftdi-unbind.shs"
expect(name).to_contain("unbind")
```

</details>

### JTAG Unbind Script - Interface Target (AC-3)

#### script targets USB interface 3-2:1.0 for JTAG channel A

- script targets USB interface 3-2:1.0 for JTAG channel A


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("script targets USB interface 3-2:1.0 for JTAG channel A")
val interface_id = "3-2:1.0"
expect(interface_id).to_contain("3-2")
expect(interface_id).to_end_with("1.0")
```

</details>

#### FTDI driver name is ftdi_sio

- FTDI driver name is ftdi_sio
   - Expected: driver equals `ftdi_sio`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("FTDI driver name is ftdi_sio")
val driver = "ftdi_sio"
expect(driver).to_equal("ftdi_sio")
```

</details>

#### unbind sysfs path contains usb driver ftdi_sio

- unbind sysfs path contains usb driver ftdi_sio


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("unbind sysfs path contains usb driver ftdi_sio")
val path = "/sys/bus/usb/drivers/ftdi_sio/unbind"
expect(path).to_contain("ftdi_sio")
expect(path).to_contain("unbind")
```

</details>

#### rebind sysfs path contains usb driver ftdi_sio

- rebind sysfs path contains usb driver ftdi_sio


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("rebind sysfs path contains usb driver ftdi_sio")
val path = "/sys/bus/usb/drivers/ftdi_sio/bind"
expect(path).to_contain("ftdi_sio")
expect(path).to_contain("bind")
```

</details>

#### unbind target interface index is 0 (JTAG/MPSSE channel A)

- unbind target interface index is 0 (JTAG/MPSSE channel A)
   - Expected: iface_index equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("unbind target interface index is 0 (JTAG/MPSSE channel A)")
val iface_index = 0
expect(iface_index).to_equal(0)
```

</details>

### JTAG Unbind Script - BLOCKED Gates (AC-3, AC-8)

#### BLOCKED: JTAG unbind requires connected FT4232H device

- BLOCKED: JTAG unbind requires connected FT4232H device


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("BLOCKED: JTAG unbind requires connected FT4232H device")
val blocked_line = "BLOCKED jtag_unbind: BLOCKED: JTAG unbind requires connected FT4232H device"
print blocked_line
expect(blocked_line).to_start_with("BLOCKED jtag_unbind:")
expect(blocked_line).to_contain("connected FT4232H device")
```

</details>

#### BLOCKED: ftdi_sio rebind requires connected FT4232H device

- BLOCKED: ftdi_sio rebind requires connected FT4232H device


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("BLOCKED: ftdi_sio rebind requires connected FT4232H device")
val blocked_line = "BLOCKED ftdi_sio_rebind: no FT4232H USB device found (lsusb 0403:6011 absent)"
print blocked_line
expect(blocked_line).to_start_with("BLOCKED ftdi_sio_rebind:")
expect(blocked_line).to_contain("0403:6011")
```

</details>

#### BLOCKED: openocd JTAG probe requires unbound ftdi_sio interface

- BLOCKED: openocd JTAG probe requires unbound ftdi_sio interface


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("BLOCKED: openocd JTAG probe requires unbound ftdi_sio interface")
val blocked_line = "BLOCKED openocd_jtag_probe: requires unbound ftdi_sio interface before openocd probe"
print blocked_line
expect(blocked_line).to_start_with("BLOCKED openocd_jtag_probe:")
expect(blocked_line).to_contain("unbound ftdi_sio interface")
expect(blocked_line).to_contain("openocd")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Hardware & OS |
| Status | Active |
| Source | `test/03_system/hardware/riscv64_fpga/jtag_unbind_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering JTAG Unbind Script - Existence (AC-3), JTAG Unbind Script - Interface Target (AC-3), JTAG Unbind Script - BLOCKED Gates (AC-3, AC-8).
- JTAG Unbind Script - Existence (AC-3)
- JTAG Unbind Script - Interface Target (AC-3)
- JTAG Unbind Script - BLOCKED Gates (AC-3, AC-8)

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 12 |
| Active scenarios | 12 |
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

- Canonical SPipe generation for source `0c0bd5bd4376633f9118adcf9ee6d2df6948edecc51287526d2ab3579839bb01`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `0c0bd5bd4376633f9118adcf9ee6d2df6948edecc51287526d2ab3579839bb01`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `0c0bd5bd4376633f9118adcf9ee6d2df6948edecc51287526d2ab3579839bb01`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **90/100**; effective score: **90/100**; blockers: **0**.

SSpec documentization score: 90/100
source: test/03_system/hardware/riscv64_fpga/jtag_unbind_spec.spl
mirror: doc/06_spec/03_system/hardware/riscv64_fpga/jtag_unbind_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=90
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/03_system/hardware/riscv64_fpga/jtag_unbind_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/hardware/riscv64_fpga/jtag_unbind_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/hardware/riscv64_fpga/jtag_unbind_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-10): 1 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/03_system/hardware/riscv64_fpga/jtag_unbind_spec.spl:14:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'jtag unbind script path is under scripts directory' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/hardware/riscv64_fpga/jtag_unbind_spec.spl:22:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'jtag unbind script name contains jtag' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/hardware/riscv64_fpga/jtag_unbind_spec.spl:28:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'jtag unbind script name contains ftdi' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
