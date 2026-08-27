# Hardware Inventory Specification

> Tests covering Hardware Inventory - Directory Structure (AC-2), Hardware Inventory - Board Model Fields (AC-2), Hardware Inventory - BLOCKED Gates (AC-2, AC-8).

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 11 | 11 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Hardware Inventory Specification

## Scenarios

### Hardware Inventory - Directory Structure (AC-2)

#### hardware tracking directory path is correct

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- hardware tracking directory path is correct


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("hardware tracking directory path is correct")
val dir = "doc/08_tracking/hardware"
expect(dir).to_start_with("doc/08_tracking")
expect(dir).to_end_with("hardware")
```

</details>

#### hardware tracking directory name is hardware

- hardware tracking directory name is hardware
   - Expected: dirname equals `hardware`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("hardware tracking directory name is hardware")
val dirname = "hardware"
expect(dirname).to_equal("hardware")
```

</details>

#### hardware manifest SDN path is correct

- hardware manifest SDN path is correct


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("hardware manifest SDN path is correct")
val path = "doc/08_tracking/hardware/hardware_manifest.sdn"
expect(path).to_contain("hardware_manifest")
expect(path).to_end_with(".sdn")
```

</details>

### Hardware Inventory - Board Model Fields (AC-2)

#### inventory board_id field name is correct

- inventory board_id field name is correct
   - Expected: field equals `board_id`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("inventory board_id field name is correct")
val field = "board_id"
expect(field).to_equal("board_id")
```

</details>

#### inventory FT4232H channel map fields are documented

- inventory FT4232H channel map fields are documented


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("inventory FT4232H channel map fields are documented")
val channel_a = "JTAG/MPSSE"
val channel_b = "ttyUSB2"
val channel_c = "ttyUSB3"
val channel_d = "ttyUSB5"
expect(channel_a).to_contain("JTAG")
expect(channel_b).to_contain("ttyUSB")
expect(channel_c).to_contain("ttyUSB")
expect(channel_d).to_contain("ttyUSB")
```

</details>

#### inventory udev interface binding field name is correct

- inventory udev interface binding field name is correct
   - Expected: field equals `jtag_interface`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("inventory udev interface binding field name is correct")
val field = "jtag_interface"
expect(field).to_equal("jtag_interface")
```

</details>

#### expected board model name is xck26-ml-carrier

- expected board model name is xck26-ml-carrier


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("expected board model name is xck26-ml-carrier")
val board_model = "xck26-ml-carrier"
expect(board_model).to_contain("xck26")
expect(board_model).to_contain("ml-carrier")
```

</details>

#### FT4232H USB vendor:product ID is 0403:6011

- FT4232H USB vendor:product ID is 0403:6011


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("FT4232H USB vendor:product ID is 0403:6011")
val usb_id = "0403:6011"
expect(usb_id).to_contain("0403")
expect(usb_id).to_contain("6011")
```

</details>

### Hardware Inventory - BLOCKED Gates (AC-2, AC-8)

#### BLOCKED: inventory log generation requires connected board

- BLOCKED: inventory log generation requires connected board


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("BLOCKED: inventory log generation requires connected board")
val blocked_line = "BLOCKED: hardware inventory requires connected board"
print blocked_line
expect(blocked_line).to_start_with("BLOCKED:")
expect(blocked_line).to_contain("hardware inventory requires connected board")
```

</details>

#### BLOCKED: udev permissions check requires connected FT4232H device

- BLOCKED: udev permissions check requires connected FT4232H device


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("BLOCKED: udev permissions check requires connected FT4232H device")
val blocked_line = "BLOCKED: no FT4232H USB device found (lsusb 0403:6011 absent)"
print blocked_line
expect(blocked_line).to_start_with("BLOCKED:")
expect(blocked_line).to_contain("FT4232H USB device")
expect(blocked_line).to_contain("0403:6011")
```

</details>

#### BLOCKED: FT4232H channel map verification requires physical device

- BLOCKED: FT4232H channel map verification requires physical device


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("BLOCKED: FT4232H channel map verification requires physical device")
val blocked_line = "BLOCKED: JTAG unbind requires connected FT4232H device"
print blocked_line
expect(blocked_line).to_start_with("BLOCKED:")
expect(blocked_line).to_contain("JTAG unbind")
expect(blocked_line).to_contain("connected FT4232H device")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Hardware & OS |
| Status | Active |
| Source | `test/03_system/hardware/riscv64_fpga/hardware_inventory_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering Hardware Inventory - Directory Structure (AC-2), Hardware Inventory - Board Model Fields (AC-2), Hardware Inventory - BLOCKED Gates (AC-2, AC-8).
- Hardware Inventory - Directory Structure (AC-2)
- Hardware Inventory - Board Model Fields (AC-2)
- Hardware Inventory - BLOCKED Gates (AC-2, AC-8)

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

- Canonical SPipe generation for source `9c41f5055cbd48109b1dbc417800f19953bf4a109b7214bbed666ce91c993796`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `9c41f5055cbd48109b1dbc417800f19953bf4a109b7214bbed666ce91c993796`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `9c41f5055cbd48109b1dbc417800f19953bf4a109b7214bbed666ce91c993796`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/03_system/hardware/riscv64_fpga/hardware_inventory_spec.spl
mirror: doc/06_spec/03_system/hardware/riscv64_fpga/hardware_inventory_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/03_system/hardware/riscv64_fpga/hardware_inventory_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/hardware/riscv64_fpga/hardware_inventory_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/hardware/riscv64_fpga/hardware_inventory_spec.spl:14:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'hardware tracking directory path is correct' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/hardware/riscv64_fpga/hardware_inventory_spec.spl:21:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'hardware tracking directory name is hardware' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/hardware/riscv64_fpga/hardware_inventory_spec.spl:27:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'hardware manifest SDN path is correct' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
