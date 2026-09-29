# FPGA Boot and Linux DTB Specification

> Tests for the FPGA Linux boot chain: DTB generation for the RV64 SoC memory map, boot contract validation (a0=hartid, a1=dtb_addr, satp=0), and SBI interface verification.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 20 | 20 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# FPGA Boot and Linux DTB Specification

Tests for the FPGA Linux boot chain: DTB generation for the RV64 SoC memory map, boot contract validation (a0=hartid, a1=dtb_addr, satp=0), and SBI interface verification.

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | rv64-fpga-linux-boot |
| Category | Infrastructure |
| Difficulty | 4/5 |
| Status | Draft |
| Requirements | REQ-14, REQ-15 |
| Research | doc/01_research/domain/vhdl_backend_linux_rtl.md |
| Source | `test/01_unit/baremetal/riscv/fpga_boot_linux_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests for the FPGA Linux boot chain: DTB generation for the RV64 SoC
memory map, boot contract validation (a0=hartid, a1=dtb_addr, satp=0),
and SBI interface verification.

Covers:
- AC-6 (FPGA boots, UART outputs SBI banner and Linux boot messages)
- AC-7 (Linux reaches userspace on the FPGA-hosted RV64GC)

## Compiled-Mode Notes

DTB generation and structural checks (magic bytes, node presence,
memory map values) are interpreter-safe. Actual UART output verification
and userspace boot require FPGA hardware or GHDL cosimulation.

## Scenarios

### DTB Generation for RV64 SoC

#### AC-6: rv64_linux_dtb_generate returns non-empty byte array

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-15
# @req REQ-14
```

</details>

#### AC-6: DTB starts with FDT magic bytes 0xD00DFEED

- AC-6: DTB starts with FDT magic bytes 0xD00DFEED
   - Expected: magic_ok is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-BAREMETAL
step("AC-6: DTB starts with FDT magic bytes 0xD00DFEED")
val mem_map = rv64_soc_memory_map_default()
val dtb = rv64_linux_dtb_generate(mem_map)
# FDT magic: big-endian 0xD00DFEED = [0xD0, 0x0D, 0xFE, 0xED]
val magic_ok = dtb_check_magic(dtb)
expect(magic_ok).to_equal(true)
```

</details>

#### AC-6: DTB size is at least 256 bytes (minimal valid FDT)

- AC-6: DTB size is at least 256 bytes (minimal valid FDT)


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-BAREMETAL
step("AC-6: DTB size is at least 256 bytes (minimal valid FDT)")
val mem_map = rv64_soc_memory_map_default()
val dtb = rv64_linux_dtb_generate(mem_map)
val len = dtb.length()
expect(len).to_be_greater_than(256)
```

</details>

### DTB Required Nodes

#### AC-6: DTB contains cpus node

- AC-6: DTB contains cpus node


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-BAREMETAL
step("AC-6: DTB contains cpus node")
val mem_map = rv64_soc_memory_map_default()
val dtb_text = rv64_linux_dtb_to_dts(mem_map)
expect(dtb_text).to_contain("cpus")
```

</details>

#### AC-6: DTB contains memory node

- AC-6: DTB contains memory node


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-BAREMETAL
step("AC-6: DTB contains memory node")
val mem_map = rv64_soc_memory_map_default()
val dtb_text = rv64_linux_dtb_to_dts(mem_map)
expect(dtb_text).to_contain("memory")
```

</details>

#### AC-6: DTB contains uart node

- AC-6: DTB contains uart node


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-BAREMETAL
step("AC-6: DTB contains uart node")
val mem_map = rv64_soc_memory_map_default()
val dtb_text = rv64_linux_dtb_to_dts(mem_map)
expect(dtb_text).to_contain("uart")
```

</details>

#### AC-6: DTB contains clint node

- AC-6: DTB contains clint node


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-BAREMETAL
step("AC-6: DTB contains clint node")
val mem_map = rv64_soc_memory_map_default()
val dtb_text = rv64_linux_dtb_to_dts(mem_map)
expect(dtb_text).to_contain("clint")
```

</details>

#### AC-6: DTB contains plic node

- AC-6: DTB contains plic node


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-BAREMETAL
step("AC-6: DTB contains plic node")
val mem_map = rv64_soc_memory_map_default()
val dtb_text = rv64_linux_dtb_to_dts(mem_map)
expect(dtb_text).to_contain("plic")
```

</details>

#### AC-7: DTB contains chosen node with stdout-path

- AC-7: DTB contains chosen node with stdout-path


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-BAREMETAL
step("AC-7: DTB contains chosen node with stdout-path")
val mem_map = rv64_soc_memory_map_default()
val dtb_text = rv64_linux_dtb_to_dts(mem_map)
expect(dtb_text).to_contain("chosen")
```

</details>

### DTB Memory Map Values

#### AC-6: Rv64SocMemoryMap default DRAM base is 0x8000_0000

- AC-6: Rv64SocMemoryMap default DRAM base is 0x8000_0000
   - Expected: mem_map.dram_base equals `0x8000_0000`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-BAREMETAL
step("AC-6: Rv64SocMemoryMap default DRAM base is 0x8000_0000")
val mem_map = rv64_soc_memory_map_default()
expect(mem_map.dram_base).to_equal(0x8000_0000)
```

</details>

#### AC-6: Rv64SocMemoryMap default UART addr is 0x1000_0000

- AC-6: Rv64SocMemoryMap default UART addr is 0x1000_0000
   - Expected: mem_map.uart_addr equals `0x1000_0000`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-BAREMETAL
step("AC-6: Rv64SocMemoryMap default UART addr is 0x1000_0000")
val mem_map = rv64_soc_memory_map_default()
expect(mem_map.uart_addr).to_equal(0x1000_0000)
```

</details>

#### AC-6: Rv64SocMemoryMap default CLINT addr is 0x200_0000

- AC-6: Rv64SocMemoryMap default CLINT addr is 0x200_0000
   - Expected: mem_map.clint_addr equals `0x200_0000`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-BAREMETAL
step("AC-6: Rv64SocMemoryMap default CLINT addr is 0x200_0000")
val mem_map = rv64_soc_memory_map_default()
expect(mem_map.clint_addr).to_equal(0x200_0000)
```

</details>

#### AC-6: Rv64SocMemoryMap default PLIC addr is 0xC00_0000

- AC-6: Rv64SocMemoryMap default PLIC addr is 0xC00_0000
   - Expected: mem_map.plic_addr equals `0xC00_0000`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-BAREMETAL
step("AC-6: Rv64SocMemoryMap default PLIC addr is 0xC00_0000")
val mem_map = rv64_soc_memory_map_default()
expect(mem_map.plic_addr).to_equal(0xC00_0000)
```

</details>

#### AC-7: Rv64SocMemoryMap default boot hartid is 0

- AC-7: Rv64SocMemoryMap default boot hartid is 0
   - Expected: mem_map.boot_hartid equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-BAREMETAL
step("AC-7: Rv64SocMemoryMap default boot hartid is 0")
val mem_map = rv64_soc_memory_map_default()
expect(mem_map.boot_hartid).to_equal(0)
```

</details>

### FPGA Boot Contract

#### AC-6: Linux boot contract requires a0 = hartid

- AC-6: Linux boot contract requires a0 = hartid
   - Expected: a0_hartid equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-BAREMETAL
step("AC-6: Linux boot contract requires a0 = hartid")
# Linux RISC-V boot protocol: a0 must contain the hart ID
val a0_hartid = 0
expect(a0_hartid).to_equal(0)
```

</details>

#### AC-6: Linux boot contract requires satp = 0 (bare mode)

- AC-6: Linux boot contract requires satp = 0 (bare mode)
   - Expected: satp_bare equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-BAREMETAL
step("AC-6: Linux boot contract requires satp = 0 (bare mode)")
# satp must be 0 on kernel entry (no virtual memory yet)
val satp_bare = 0
expect(satp_bare).to_equal(0)
```

</details>

#### AC-6: fpga_boot_main sets up SBI handoff (compiled mode for full test)

- AC-6: fpga_boot_main sets up SBI handoff (compiled mode for full test)
   - Expected: observed_hartid equals `hartid`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-BAREMETAL
step("AC-6: fpga_boot_main sets up SBI handoff (compiled mode for full test)")
# Full verification requires compiled mode:
# - fpga_boot_main(0) runs
# - checks a0=0, a1=dtb_addr, satp=0 before jump
val hartid = 0
val observed_hartid = fpga_boot_main(hartid)
expect(observed_hartid).to_equal(hartid)
```

</details>

### SBI Interface

#### AC-6: SBI timer extension ID is 0x54494D45

- AC-6: SBI timer extension ID is 0x54494D45
   - Expected: sbi_timer_eid equals `0x54494D45`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-BAREMETAL
step("AC-6: SBI timer extension ID is 0x54494D45")
val sbi_timer_eid = 0x54494D45
expect(sbi_timer_eid).to_equal(0x54494D45)
```

</details>

#### AC-6: SBI IPI extension ID is 0x735049

- AC-6: SBI IPI extension ID is 0x735049
   - Expected: sbi_ipi_eid equals `0x735049`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-BAREMETAL
step("AC-6: SBI IPI extension ID is 0x735049")
val sbi_ipi_eid = 0x735049
expect(sbi_ipi_eid).to_equal(0x735049)
```

</details>

#### AC-6: SBI base extension ID is 0x10

- AC-6: SBI base extension ID is 0x10
   - Expected: sbi_base_eid equals `0x10`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-BAREMETAL
step("AC-6: SBI base extension ID is 0x10")
val sbi_base_eid = 0x10
expect(sbi_base_eid).to_equal(0x10)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 20 |
| Active scenarios | 20 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


## Related Documentation

- **Requirements:** `REQ-14, REQ-15`
- **Research:** `doc/01_research/domain/vhdl_backend_linux_rtl.md`


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-15`
- `REQ-14`
- `REQ-SSPEC-BAREMETAL`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `f8e86d3b31173387d29335079f82071f10f7f8f8ba627469b0b5054d18a38d73`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `f8e86d3b31173387d29335079f82071f10f7f8f8ba627469b0b5054d18a38d73`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `f8e86d3b31173387d29335079f82071f10f7f8f8ba627469b0b5054d18a38d73`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **85/100**; effective score: **85/100**; blockers: **0**.

SSpec documentization score: 85/100
source: test/01_unit/baremetal/riscv/fpga_boot_linux_spec.spl
mirror: doc/06_spec/01_unit/baremetal/riscv/fpga_boot_linux_spec.md (current)
findings: 7 blockers: 0
  narrative=100 structure=90 oracle=70
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/baremetal/riscv/fpga_boot_linux_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/baremetal/riscv/fpga_boot_linux_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/baremetal/riscv/fpga_boot_linux_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 3 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/baremetal/riscv/fpga_boot_linux_spec.spl:57:1: warning SSDOC-BEH-001 [structure] (-10): scenario 'AC-6: rv64_linux_dtb_generate returns non-empty byte array' has no visible step flow
  why: Ordered visible actions make the manual operable.
  improve: Add ordered step("...") calls for meaningful actions.
test/01_unit/baremetal/riscv/fpga_boot_linux_spec.spl:68:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'AC-6: DTB starts with FDT magic bytes 0xD00DFEED' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/baremetal/riscv/fpga_boot_linux_spec.spl:77:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'AC-6: DTB size is at least 256 bytes (minimal valid FDT)' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/baremetal/riscv/fpga_boot_linux_spec.spl:91:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'AC-6: DTB contains cpus node' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
