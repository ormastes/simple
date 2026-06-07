# Rvfi Specification

> 1. expect ports len

<!-- sdn-diagram:id=rvfi_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=rvfi_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

rvfi_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=rvfi_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 11 | 11 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Rvfi Specification

## Scenarios

### RV32I RVFI manifest

#### lists standard RVFI output ports

1. expect ports len


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val ports = rvfi_port_manifest()
expect ports.len() == 17
expect ports[0].name == "rvfi_valid"
expect ports[2].name == "rvfi_insn"
```

</details>

#### renders formal wrapper port comments

1. check
2. check
3. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val text = rvfi_formal_wrapper_ports("rv32i_core")
check(text.contains("rvfi_valid"))
check(text.contains("rvfi_mem_wdata"))
check(text.contains("std_logic_vector(31 downto 0)"))
```

</details>

#### renders VHDL scalar and vector port types

1. expect rvfi vhdl type
2. expect rvfi vhdl type


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect rvfi_vhdl_type(1) == "std_logic"
expect rvfi_vhdl_type(32) == "std_logic_vector(31 downto 0)"
```

</details>

#### renders an RVFI formal VHDL wrapper

1. check
2. check
3. check
4. check
5. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val text = rvfi_formal_wrapper_vhdl("rv32i_core_rvfi", "rv32i_core")
check(text.contains("entity rv32i_core_rvfi is"))
check(text.contains("dut: entity work.rv32i_core"))
check(text.contains("rvfi_valid : out std_logic"))
check(text.contains("rvfi_order : out std_logic_vector(63 downto 0)"))
check(text.contains("rvfi_mem_wdata => rvfi_mem_wdata"))
```

</details>

#### reports missing RVFI ports before formal flow runs

1. expect missing len
2. check
3. check
4. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val entity = "entity rv32i_core is port (clk : in std_logic; reset_n : in std_logic); end entity;"
val missing = rvfi_missing_vhdl_ports(entity)
expect missing.len() == 17
expect missing[0] == "rvfi_valid"
val readiness = rvfi_formal_readiness("rv32i_core", entity)
check(not readiness.ready)
check(readiness.message.contains("missing 17 RVFI ports"))
check(rvfi_render_formal_readiness(readiness).contains("- rvfi_mem_wdata"))
```

</details>

#### accepts a VHDL entity with the full RVFI manifest

1. check
2. expect readiness missing ports len


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val wrapper = rvfi_formal_wrapper_vhdl("rv32i_core_rvfi", "rv32i_core")
val readiness = rvfi_formal_readiness("rv32i_core_rvfi", wrapper)
check(readiness.ready)
expect readiness.missing_ports.len() == 0
```

</details>

### RV32I RVFI trace

#### captures one retired instruction when RVFI is enabled

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val trace = rvfi_trace_from_snapshot(rvfi_enabled_config(7), 3, snapshot_sample())
check(trace.rvfi_valid)
expect trace.rvfi_order == 10
expect trace.rvfi_insn == 0x00108293
expect trace.rvfi_pc_rdata == 0x1000
expect trace.rvfi_pc_wdata == 0x1004
expect trace.rvfi_rd_addr == 5
expect trace.rvfi_rd_wdata == 14
```

</details>

#### suppresses valid when RVFI is disabled

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val trace = rvfi_trace_from_snapshot(rvfi_disabled_config(), 0, snapshot_sample())
check(not trace.rvfi_valid)
```

</details>

#### computes byte masks from memory width

1. expect rvfi mask for width
2. expect rvfi mask for width
3. expect rvfi mask for width


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect rvfi_mask_for_width(0) == 0x1
expect rvfi_mask_for_width(1) == 0x3
expect rvfi_mask_for_width(2) == 0xF
```

</details>

#### extracts RVFI snapshot from the actual core datapath

1. check
2. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val insn = 0x00108293  # addi x5, x1, 1
val rf0 = regfile_create()
val rf1 = regfile_write(rf0, 1, 41, true)
val state = core_reset(0x1000)
val comb = core_combinational(state, insn, 0, rf1)
val snapshot = core_rvfi_snapshot(state, insn, 0, comb)
expect snapshot.pc == 0x1000
expect snapshot.pc_next == 0x1004
expect snapshot.rs1_addr == 1
expect snapshot.rs1_rdata == 41
expect snapshot.rd_addr == 5
expect snapshot.rd_wdata == 42
check(not snapshot.dmem_re)
check(not snapshot.dmem_we)
```

</details>

#### builds optional RVFI output from core signals

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val insn = 0x00108293  # addi x5, x1, 1
val rf0 = regfile_create()
val rf1 = regfile_write(rf0, 1, 6, true)
val state = core_reset(0x2000)
val comb = core_combinational(state, insn, 0, rf1)
val trace = core_rvfi_trace(rvfi_enabled_config(100), 2, state, insn, 0, comb)
check(trace.rvfi_valid)
expect trace.rvfi_order == 102
expect trace.rvfi_insn == insn
expect trace.rvfi_pc_rdata == 0x2000
expect trace.rvfi_pc_wdata == 0x2004
expect trace.rvfi_rd_addr == 5
expect trace.rvfi_rd_wdata == 7
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Hardware & OS |
| Status | Active |
| Source | `test/01_unit/hardware/rv32i_rtl/rvfi_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- RV32I RVFI manifest
- RV32I RVFI trace

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 11 |
| Active scenarios | 11 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
