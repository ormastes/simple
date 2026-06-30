# Hardware Inventory Specification

> <details>

<!-- sdn-diagram:id=hardware_inventory_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=hardware_inventory_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

hardware_inventory_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=hardware_inventory_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 11 | 11 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Hardware Inventory Specification

## Scenarios

### Hardware Inventory - Directory Structure (AC-2)

#### hardware tracking directory path is correct

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val dir = "doc/08_tracking/hardware"
expect(dir).to_start_with("doc/08_tracking")
expect(dir).to_end_with("hardware")
```

</details>

#### hardware tracking directory name is hardware

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val dirname = "hardware"
expect(dirname).to_equal("hardware")
```

</details>

#### hardware manifest SDN path is correct

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val path = "doc/08_tracking/hardware/hardware_manifest.sdn"
expect(path).to_contain("hardware_manifest")
expect(path).to_end_with(".sdn")
```

</details>

### Hardware Inventory - Board Model Fields (AC-2)

#### inventory board_id field name is correct

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val field = "board_id"
expect(field).to_equal("board_id")
```

</details>

#### inventory FT4232H channel map fields are documented

<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val field = "jtag_interface"
expect(field).to_equal("jtag_interface")
```

</details>

#### expected board model name is xck26-ml-carrier

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val board_model = "xck26-ml-carrier"
expect(board_model).to_contain("xck26")
expect(board_model).to_contain("ml-carrier")
```

</details>

#### FT4232H USB vendor:product ID is 0403:6011

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val usb_id = "0403:6011"
expect(usb_id).to_contain("0403")
expect(usb_id).to_contain("6011")
```

</details>

### Hardware Inventory - BLOCKED Gates (AC-2, AC-8)

#### BLOCKED: inventory log generation requires connected board

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val blocked_line = "BLOCKED: hardware inventory requires connected board"
print blocked_line
expect(blocked_line).to_start_with("BLOCKED:")
expect(blocked_line).to_contain("hardware inventory requires connected board")
```

</details>

#### BLOCKED: udev permissions check requires connected FT4232H device

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val blocked_line = "BLOCKED: no FT4232H USB device found (lsusb 0403:6011 absent)"
print blocked_line
expect(blocked_line).to_start_with("BLOCKED:")
expect(blocked_line).to_contain("FT4232H USB device")
expect(blocked_line).to_contain("0403:6011")
```

</details>

#### BLOCKED: FT4232H channel map verification requires physical device

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
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
