# Platform Capsule Specification

> Tests covering Platform Capsule - fpga.spl (AC-4), Platform Capsule - manifest.spl (AC-4), Platform Capsule - uart_mmio.spl (AC-4), Platform Capsule - timer_mmio.spl (AC-4), Platform Capsule - Module Count (AC-4).

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 9 | 9 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Platform Capsule Specification

## Scenarios

### Platform Capsule - fpga.spl (AC-4)

#### fpga.spl exists in the riscv64 platform capsule

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- fpga.spl exists in the riscv64 platform capsule


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("fpga.spl exists in the riscv64 platform capsule")
val src = capsule_source("fpga.spl")
expect(src.len()).to_be_greater_than(0)
```

</details>

#### fpga.spl declares the platform init entry point

- fpga.spl declares the platform init entry point


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("fpga.spl declares the platform init entry point")
val src = capsule_source("fpga.spl")
expect(src).to_contain("fn fpga_platform_init():")
```

</details>

### Platform Capsule - manifest.spl (AC-4)

#### manifest.spl exists in the riscv64 platform capsule

- manifest.spl exists in the riscv64 platform capsule


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("manifest.spl exists in the riscv64 platform capsule")
val src = capsule_source("manifest.spl")
expect(src.len()).to_be_greater_than(0)
```

</details>

#### manifest.spl declares BoardConfig and its loaders

- manifest.spl declares BoardConfig and its loaders


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("manifest.spl declares BoardConfig and its loaders")
val src = capsule_source("manifest.spl")
expect(src).to_contain("struct BoardConfig:")
expect(src).to_contain("fn default_board_config() -> BoardConfig:")
expect(src).to_contain("fn load_board_config() -> BoardConfig:")
```

</details>

### Platform Capsule - uart_mmio.spl (AC-4)

#### uart_mmio.spl exists in the riscv64 platform capsule

- uart_mmio.spl exists in the riscv64 platform capsule


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("uart_mmio.spl exists in the riscv64 platform capsule")
val src = capsule_source("uart_mmio.spl")
expect(src.len()).to_be_greater_than(0)
```

</details>

#### uart_mmio.spl declares the MMIO UART surface

- uart_mmio.spl declares the MMIO UART surface


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("uart_mmio.spl declares the MMIO UART surface")
val src = capsule_source("uart_mmio.spl")
expect(src).to_contain("fn uart_mmio_init(base: u64, baud: u64):")
expect(src).to_contain("fn uart_mmio_putchar(base: u64, ch: u8):")
expect(src).to_contain("fn uart_mmio_puts(base: u64, msg: text):")
```

</details>

### Platform Capsule - timer_mmio.spl (AC-4)

#### timer_mmio.spl exists in the riscv64 platform capsule

- timer_mmio.spl exists in the riscv64 platform capsule


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("timer_mmio.spl exists in the riscv64 platform capsule")
val src = capsule_source("timer_mmio.spl")
expect(src.len()).to_be_greater_than(0)
```

</details>

#### timer_mmio.spl declares the CLINT timer surface

- timer_mmio.spl declares the CLINT timer surface


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("timer_mmio.spl declares the CLINT timer surface")
val src = capsule_source("timer_mmio.spl")
expect(src).to_contain("fn timer_mmio_init(clint_base: u64):")
expect(src).to_contain("fn timer_read_mtime(clint_base: u64) -> u64:")
expect(src).to_contain("fn timer_polling_delay_ms(clint_base: u64, timebase_hz: u64, ms: u64):")
```

</details>

### Platform Capsule - Module Count (AC-4)

#### all four required capsule files are present and non-empty

- all four required capsule files are present and non-empty
   - Expected: files.len() equals `4`
   - Expected: present equals `4`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("all four required capsule files are present and non-empty")
val files = ["fpga.spl", "manifest.spl", "uart_mmio.spl", "timer_mmio.spl"]
expect(files.len()).to_equal(4)
var present = 0
for f in files:
    if capsule_source(f).len() > 0:
        present = present + 1
expect(present).to_equal(4)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Hardware & OS |
| Status | Active |
| Source | `test/03_system/hardware/riscv64_fpga/platform_capsule_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering Platform Capsule - fpga.spl (AC-4), Platform Capsule - manifest.spl (AC-4), Platform Capsule - uart_mmio.spl (AC-4), Platform Capsule - timer_mmio.spl (AC-4), Platform Capsule - Module Count (AC-4).
- Platform Capsule - fpga.spl (AC-4)
- Platform Capsule - manifest.spl (AC-4)
- Platform Capsule - uart_mmio.spl (AC-4)
- Platform Capsule - timer_mmio.spl (AC-4)
- Platform Capsule - Module Count (AC-4)

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 9 |
| Active scenarios | 9 |
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

- Canonical SPipe generation for source `ea949a432190091fd20e6624229d2feed9c85b9d094eae217ec5b6628e1fccf1`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `ea949a432190091fd20e6624229d2feed9c85b9d094eae217ec5b6628e1fccf1`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `ea949a432190091fd20e6624229d2feed9c85b9d094eae217ec5b6628e1fccf1`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **88/100**; effective score: **88/100**; blockers: **0**.

SSpec documentization score: 88/100
source: test/03_system/hardware/riscv64_fpga/platform_capsule_spec.spl
mirror: doc/06_spec/03_system/hardware/riscv64_fpga/platform_capsule_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=80
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/03_system/hardware/riscv64_fpga/platform_capsule_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/hardware/riscv64_fpga/platform_capsule_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/hardware/riscv64_fpga/platform_capsule_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-20): 2 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/03_system/hardware/riscv64_fpga/platform_capsule_spec.spl:28:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'fpga.spl exists in the riscv64 platform capsule' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/hardware/riscv64_fpga/platform_capsule_spec.spl:34:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'fpga.spl declares the platform init entry point' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/hardware/riscv64_fpga/platform_capsule_spec.spl:41:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'manifest.spl exists in the riscv64 platform capsule' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
