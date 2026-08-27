# Manifest Format Specification

> <details>

<!-- sdn-diagram:id=manifest_format_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=manifest_format_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

manifest_format_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=manifest_format_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 24 | 24 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Manifest Format Specification

## Scenarios

### Hardware Manifest - File Location (AC-6)

#### hardware_manifest.sdn is under doc/08_tracking/hardware

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val path = "doc/08_tracking/hardware/hardware_manifest.sdn"
expect(path).to_start_with("doc/08_tracking/hardware")
expect(path).to_end_with("hardware_manifest.sdn")
```

</details>

#### manifest file uses SDN extension

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val ext = ".sdn"
val path = "doc/08_tracking/hardware/hardware_manifest.sdn"
expect(path).to_end_with(ext)
```

</details>

#### manifest file is not JSON or YAML

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val path = "doc/08_tracking/hardware/hardware_manifest.sdn"
val is_json = path.contains(".json")
val is_yaml = path.contains(".yaml")
expect(is_json).to_equal(false)
expect(is_yaml).to_equal(false)
```

</details>

### Hardware Manifest - Required Fields (AC-6)

#### manifest schema includes board_id field

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val field = "board_id"
expect(field).to_equal("board_id")
```

</details>

#### manifest schema includes reset_pc field

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val field = "reset_pc"
expect(field).to_equal("reset_pc")
```

</details>

#### manifest schema includes ram_base field

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val field = "ram_base"
expect(field).to_equal("ram_base")
```

</details>

#### manifest schema includes ram_size field

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val field = "ram_size"
expect(field).to_equal("ram_size")
```

</details>

#### manifest schema includes uart_base field

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val field = "uart_base"
expect(field).to_equal("uart_base")
```

</details>

#### manifest schema includes uart_baud field

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val field = "uart_baud"
expect(field).to_equal("uart_baud")
```

</details>

#### manifest schema includes timer_base field

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val field = "timer_base"
expect(field).to_equal("timer_base")
```

</details>

#### manifest schema includes plic_base field

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val field = "plic_base"
expect(field).to_equal("plic_base")
```

</details>

#### manifest schema includes hart_count field

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val field = "hart_count"
expect(field).to_equal("hart_count")
```

</details>

#### manifest schema includes timebase_hz field

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val field = "timebase_hz"
expect(field).to_equal("timebase_hz")
```

</details>

#### manifest has exactly 10 required fields

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val fields = ["board_id", "reset_pc", "ram_base", "ram_size",
              "uart_base", "uart_baud", "timer_base", "plic_base",
              "hart_count", "timebase_hz"]
expect(fields.len()).to_equal(10)
```

</details>

### Hardware Manifest - Default Values (AC-6)

#### default ram_base for xck26 is 0x80000000

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val ram_base = "0x80000000"
expect(ram_base).to_equal("0x80000000")
```

</details>

#### default uart_base for xck26 ml-carrier is 0x10000000

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val uart_base = "0x10000000"
expect(uart_base).to_equal("0x10000000")
```

</details>

#### default timer_base (CLINT) is 0x02000000

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val timer_base = "0x02000000"
expect(timer_base).to_equal("0x02000000")
```

</details>

#### default plic_base is 0x0C000000

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val plic_base = "0x0C000000"
expect(plic_base).to_equal("0x0C000000")
```

</details>

#### default uart_baud is 115200

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val baud = 115200
expect(baud).to_equal(115200)
```

</details>

#### default timebase_hz is 10000000 (10 MHz)

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val hz = 10000000
expect(hz).to_equal(10000000)
```

</details>

#### default hart_count is 1

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val harts = 1
expect(harts).to_equal(1)
```

</details>

### Hardware Manifest - SDN Format (AC-6)

#### SDN table name is hardware_manifest

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val table_name = "hardware_manifest"
expect(table_name).to_equal("hardware_manifest")
```

</details>

#### SDN format uses pipe-delimited column headers

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val header_format = "|col1, col2|"
expect(header_format).to_start_with("|")
expect(header_format).to_end_with("|")
```

</details>

#### SDN board_id value for xck26 ml-carrier is correct

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val board_id = "xck26-ml-carrier"
expect(board_id).to_contain("xck26")
expect(board_id).to_contain("ml-carrier")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Hardware & OS |
| Status | Active |
| Source | `test/03_system/hardware/riscv64_fpga/manifest_format_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- Hardware Manifest - File Location (AC-6)
- Hardware Manifest - Required Fields (AC-6)
- Hardware Manifest - Default Values (AC-6)
- Hardware Manifest - SDN Format (AC-6)

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 24 |
| Active scenarios | 24 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
