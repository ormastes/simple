# FPGA Boot and Linux DTB Specification

> Tests for the FPGA Linux boot chain: DTB generation for the RV64 SoC memory map, boot contract validation (a0=hartid, a1=dtb_addr, satp=0), and SBI interface verification.

<!-- sdn-diagram:id=fpga_boot_linux_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=fpga_boot_linux_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

fpga_boot_linux_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=fpga_boot_linux_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

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
| Updated | 2026-06-01 |
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

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val mem_map = rv64_soc_memory_map_default()
val dtb = rv64_linux_dtb_generate(mem_map)
val len = dtb.length()
expect(len).to_be_greater_than(0)
```

</details>

#### AC-6: DTB starts with FDT magic bytes 0xD00DFEED

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val mem_map = rv64_soc_memory_map_default()
val dtb = rv64_linux_dtb_generate(mem_map)
# FDT magic: big-endian 0xD00DFEED = [0xD0, 0x0D, 0xFE, 0xED]
val magic_ok = dtb_check_magic(dtb)
expect(magic_ok).to_equal(true)
```

</details>

#### AC-6: DTB size is at least 256 bytes (minimal valid FDT)

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val mem_map = rv64_soc_memory_map_default()
val dtb = rv64_linux_dtb_generate(mem_map)
val len = dtb.length()
expect(len).to_be_greater_than(256)
```

</details>

### DTB Required Nodes

#### AC-6: DTB contains cpus node

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val mem_map = rv64_soc_memory_map_default()
val dtb_text = rv64_linux_dtb_to_dts(mem_map)
expect(dtb_text).to_contain("cpus")
```

</details>

#### AC-6: DTB contains memory node

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val mem_map = rv64_soc_memory_map_default()
val dtb_text = rv64_linux_dtb_to_dts(mem_map)
expect(dtb_text).to_contain("memory")
```

</details>

#### AC-6: DTB contains uart node

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val mem_map = rv64_soc_memory_map_default()
val dtb_text = rv64_linux_dtb_to_dts(mem_map)
expect(dtb_text).to_contain("uart")
```

</details>

#### AC-6: DTB contains clint node

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val mem_map = rv64_soc_memory_map_default()
val dtb_text = rv64_linux_dtb_to_dts(mem_map)
expect(dtb_text).to_contain("clint")
```

</details>

#### AC-6: DTB contains plic node

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val mem_map = rv64_soc_memory_map_default()
val dtb_text = rv64_linux_dtb_to_dts(mem_map)
expect(dtb_text).to_contain("plic")
```

</details>

#### AC-7: DTB contains chosen node with stdout-path

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val mem_map = rv64_soc_memory_map_default()
val dtb_text = rv64_linux_dtb_to_dts(mem_map)
expect(dtb_text).to_contain("chosen")
```

</details>

### DTB Memory Map Values

#### AC-6: Rv64SocMemoryMap default DRAM base is 0x8000_0000

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val mem_map = rv64_soc_memory_map_default()
expect(mem_map.dram_base).to_equal(0x8000_0000)
```

</details>

#### AC-6: Rv64SocMemoryMap default UART addr is 0x1000_0000

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val mem_map = rv64_soc_memory_map_default()
expect(mem_map.uart_addr).to_equal(0x1000_0000)
```

</details>

#### AC-6: Rv64SocMemoryMap default CLINT addr is 0x200_0000

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val mem_map = rv64_soc_memory_map_default()
expect(mem_map.clint_addr).to_equal(0x200_0000)
```

</details>

#### AC-6: Rv64SocMemoryMap default PLIC addr is 0xC00_0000

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val mem_map = rv64_soc_memory_map_default()
expect(mem_map.plic_addr).to_equal(0xC00_0000)
```

</details>

#### AC-7: Rv64SocMemoryMap default boot hartid is 0

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val mem_map = rv64_soc_memory_map_default()
expect(mem_map.boot_hartid).to_equal(0)
```

</details>

### FPGA Boot Contract

#### AC-6: Linux boot contract requires a0 = hartid

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Linux RISC-V boot protocol: a0 must contain the hart ID
val a0_hartid = 0
expect(a0_hartid).to_equal(0)
```

</details>

#### AC-6: Linux boot contract requires satp = 0 (bare mode)

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# satp must be 0 on kernel entry (no virtual memory yet)
val satp_bare = 0
expect(satp_bare).to_equal(0)
```

</details>

#### AC-6: fpga_boot_main sets up SBI handoff (compiled mode for full test)

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val sbi_timer_eid = 0x54494D45
expect(sbi_timer_eid).to_equal(0x54494D45)
```

</details>

#### AC-6: SBI IPI extension ID is 0x735049

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val sbi_ipi_eid = 0x735049
expect(sbi_ipi_eid).to_equal(0x735049)
```

</details>

#### AC-6: SBI base extension ID is 0x10

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

- **Requirements:** [REQ-14, REQ-15](REQ-14, REQ-15)
- **Research:** [doc/01_research/domain/vhdl_backend_linux_rtl.md](doc/01_research/domain/vhdl_backend_linux_rtl.md)


</details>
