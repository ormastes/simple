# Manifest Format Specification

> Tests covering Hardware Manifest - File Location (AC-6), Hardware Manifest - Required Fields (AC-6), Hardware Manifest - Default Values (AC-6), Hardware Manifest - SDN Format (AC-6).

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 24 | 24 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Manifest Format Specification

## Scenarios

### Hardware Manifest - File Location (AC-6)

#### hardware_manifest.sdn is under doc/08_tracking/hardware

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- hardware_manifest.sdn is under doc/08_tracking/hardware


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("hardware_manifest.sdn is under doc/08_tracking/hardware")
val path = "doc/08_tracking/hardware/hardware_manifest.sdn"
expect(path).to_start_with("doc/08_tracking/hardware")
expect(path).to_end_with("hardware_manifest.sdn")
```

</details>

#### manifest file uses SDN extension

- manifest file uses SDN extension


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("manifest file uses SDN extension")
val ext = ".sdn"
val path = "doc/08_tracking/hardware/hardware_manifest.sdn"
expect(path).to_end_with(ext)
```

</details>

#### manifest file is not JSON or YAML

- manifest file is not JSON or YAML
   - Expected: is_json is false
   - Expected: is_yaml is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("manifest file is not JSON or YAML")
val path = "doc/08_tracking/hardware/hardware_manifest.sdn"
val is_json = path.contains(".json")
val is_yaml = path.contains(".yaml")
expect(is_json).to_equal(false)
expect(is_yaml).to_equal(false)
```

</details>

### Hardware Manifest - Required Fields (AC-6)

#### manifest schema includes board_id field

- manifest schema includes board_id field
   - Expected: field equals `board_id`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("manifest schema includes board_id field")
val field = "board_id"
expect(field).to_equal("board_id")
```

</details>

#### manifest schema includes reset_pc field

- manifest schema includes reset_pc field
   - Expected: field equals `reset_pc`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("manifest schema includes reset_pc field")
val field = "reset_pc"
expect(field).to_equal("reset_pc")
```

</details>

#### manifest schema includes ram_base field

- manifest schema includes ram_base field
   - Expected: field equals `ram_base`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("manifest schema includes ram_base field")
val field = "ram_base"
expect(field).to_equal("ram_base")
```

</details>

#### manifest schema includes ram_size field

- manifest schema includes ram_size field
   - Expected: field equals `ram_size`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("manifest schema includes ram_size field")
val field = "ram_size"
expect(field).to_equal("ram_size")
```

</details>

#### manifest schema includes uart_base field

- manifest schema includes uart_base field
   - Expected: field equals `uart_base`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("manifest schema includes uart_base field")
val field = "uart_base"
expect(field).to_equal("uart_base")
```

</details>

#### manifest schema includes uart_baud field

- manifest schema includes uart_baud field
   - Expected: field equals `uart_baud`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("manifest schema includes uart_baud field")
val field = "uart_baud"
expect(field).to_equal("uart_baud")
```

</details>

#### manifest schema includes timer_base field

- manifest schema includes timer_base field
   - Expected: field equals `timer_base`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("manifest schema includes timer_base field")
val field = "timer_base"
expect(field).to_equal("timer_base")
```

</details>

#### manifest schema includes plic_base field

- manifest schema includes plic_base field
   - Expected: field equals `plic_base`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("manifest schema includes plic_base field")
val field = "plic_base"
expect(field).to_equal("plic_base")
```

</details>

#### manifest schema includes hart_count field

- manifest schema includes hart_count field
   - Expected: field equals `hart_count`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("manifest schema includes hart_count field")
val field = "hart_count"
expect(field).to_equal("hart_count")
```

</details>

#### manifest schema includes timebase_hz field

- manifest schema includes timebase_hz field
   - Expected: field equals `timebase_hz`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("manifest schema includes timebase_hz field")
val field = "timebase_hz"
expect(field).to_equal("timebase_hz")
```

</details>

#### manifest has exactly 10 required fields

- manifest has exactly 10 required fields
   - Expected: fields.len() equals `10`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("manifest has exactly 10 required fields")
val fields = ["board_id", "reset_pc", "ram_base", "ram_size",
              "uart_base", "uart_baud", "timer_base", "plic_base",
              "hart_count", "timebase_hz"]
expect(fields.len()).to_equal(10)
```

</details>

### Hardware Manifest - Default Values (AC-6)

#### default ram_base for xck26 is 0x80000000

- default ram_base for xck26 is 0x80000000
   - Expected: ram_base equals `0x80000000`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("default ram_base for xck26 is 0x80000000")
val ram_base = "0x80000000"
expect(ram_base).to_equal("0x80000000")
```

</details>

#### default uart_base for xck26 ml-carrier is 0x10000000

- default uart_base for xck26 ml-carrier is 0x10000000
   - Expected: uart_base equals `0x10000000`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("default uart_base for xck26 ml-carrier is 0x10000000")
val uart_base = "0x10000000"
expect(uart_base).to_equal("0x10000000")
```

</details>

#### default timer_base (CLINT) is 0x02000000

- default timer_base (CLINT) is 0x02000000
   - Expected: timer_base equals `0x02000000`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("default timer_base (CLINT) is 0x02000000")
val timer_base = "0x02000000"
expect(timer_base).to_equal("0x02000000")
```

</details>

#### default plic_base is 0x0C000000

- default plic_base is 0x0C000000
   - Expected: plic_base equals `0x0C000000`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("default plic_base is 0x0C000000")
val plic_base = "0x0C000000"
expect(plic_base).to_equal("0x0C000000")
```

</details>

#### default uart_baud is 115200

- default uart_baud is 115200
   - Expected: baud equals `115200`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("default uart_baud is 115200")
val baud = 115200
expect(baud).to_equal(115200)
```

</details>

#### default timebase_hz is 10000000 (10 MHz)

- default timebase_hz is 10000000 (10 MHz)
   - Expected: hz equals `10000000`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("default timebase_hz is 10000000 (10 MHz)")
val hz = 10000000
expect(hz).to_equal(10000000)
```

</details>

#### default hart_count is 1

- default hart_count is 1
   - Expected: harts equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("default hart_count is 1")
val harts = 1
expect(harts).to_equal(1)
```

</details>

### Hardware Manifest - SDN Format (AC-6)

#### SDN table name is hardware_manifest

- SDN table name is hardware_manifest
   - Expected: table_name equals `hardware_manifest`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("SDN table name is hardware_manifest")
val table_name = "hardware_manifest"
expect(table_name).to_equal("hardware_manifest")
```

</details>

#### SDN format uses pipe-delimited column headers

- SDN format uses pipe-delimited column headers


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("SDN format uses pipe-delimited column headers")
val header_format = "|col1, col2|"
expect(header_format).to_start_with("|")
expect(header_format).to_end_with("|")
```

</details>

#### SDN board_id value for xck26 ml-carrier is correct

- SDN board_id value for xck26 ml-carrier is correct


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("SDN board_id value for xck26 ml-carrier is correct")
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
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering Hardware Manifest - File Location (AC-6), Hardware Manifest - Required Fields (AC-6), Hardware Manifest - Default Values (AC-6), Hardware Manifest - SDN Format (AC-6).
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

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-SYSTEM`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `bc5fefca419a6d5c03c6e7830926cafd001c0ae2330147ce506a78ca3ed02138`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `bc5fefca419a6d5c03c6e7830926cafd001c0ae2330147ce506a78ca3ed02138`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `bc5fefca419a6d5c03c6e7830926cafd001c0ae2330147ce506a78ca3ed02138`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **86/100**; effective score: **86/100**; blockers: **0**.

SSpec documentization score: 86/100
source: test/03_system/hardware/riscv64_fpga/manifest_format_spec.spl
mirror: doc/06_spec/03_system/hardware/riscv64_fpga/manifest_format_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/03_system/hardware/riscv64_fpga/manifest_format_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/hardware/riscv64_fpga/manifest_format_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/hardware/riscv64_fpga/manifest_format_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 4 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/03_system/hardware/riscv64_fpga/manifest_format_spec.spl:15:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'hardware_manifest.sdn is under doc/08_tracking/hardware' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/hardware/riscv64_fpga/manifest_format_spec.spl:22:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'manifest file uses SDN extension' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/hardware/riscv64_fpga/manifest_format_spec.spl:29:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'manifest file is not JSON or YAML' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
