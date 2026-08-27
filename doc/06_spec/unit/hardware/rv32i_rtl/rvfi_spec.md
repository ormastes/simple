# Rvfi Specification

> Tests covering RV32I RVFI manifest, RV32I RVFI trace.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 9 | 9 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Rvfi Specification

## Scenarios

### RV32I RVFI manifest

#### lists standard RVFI output ports

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- lists standard RVFI output ports


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("lists standard RVFI output ports")
val ports = rvfi_port_manifest()
expect ports.len() == 17
expect ports[0].name == "rvfi_valid"
expect ports[2].name == "rvfi_insn"
```

</details>

#### renders formal wrapper port comments

- renders formal wrapper port comments


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("renders formal wrapper port comments")
val text = rvfi_formal_wrapper_ports("rv32i_core")
check(text.contains("rvfi_valid"))
check(text.contains("rvfi_mem_wdata"))
check(text.contains("std_logic_vector(31 downto 0)"))
```

</details>

#### renders VHDL scalar and vector port types

- renders VHDL scalar and vector port types


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("renders VHDL scalar and vector port types")
expect rvfi_vhdl_type(1) == "std_logic"
expect rvfi_vhdl_type(32) == "std_logic_vector(31 downto 0)"
```

</details>

#### renders an RVFI formal VHDL wrapper

- renders an RVFI formal VHDL wrapper


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("renders an RVFI formal VHDL wrapper")
val text = rvfi_formal_wrapper_vhdl("rv32i_core_rvfi", "rv32i_core")
check(text.contains("entity rv32i_core_rvfi is"))
check(text.contains("dut: entity work.rv32i_core"))
check(text.contains("rvfi_valid : out std_logic"))
check(text.contains("rvfi_order : out std_logic_vector(63 downto 0)"))
check(text.contains("rvfi_mem_wdata => rvfi_mem_wdata"))
```

</details>

### RV32I RVFI trace

#### captures one retired instruction when RVFI is enabled

- captures one retired instruction when RVFI is enabled


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("captures one retired instruction when RVFI is enabled")
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

- suppresses valid when RVFI is disabled


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("suppresses valid when RVFI is disabled")
val trace = rvfi_trace_from_snapshot(rvfi_disabled_config(), 0, snapshot_sample())
check(not trace.rvfi_valid)
```

</details>

#### computes byte masks from memory width

- computes byte masks from memory width


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("computes byte masks from memory width")
expect rvfi_mask_for_width(0) == 0x1
expect rvfi_mask_for_width(1) == 0x3
expect rvfi_mask_for_width(2) == 0xF
```

</details>

#### extracts RVFI snapshot from the actual core datapath

- extracts RVFI snapshot from the actual core datapath


<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("extracts RVFI snapshot from the actual core datapath")
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

- builds optional RVFI output from core signals


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("builds optional RVFI output from core signals")
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
| Source | `test/unit/hardware/rv32i_rtl/rvfi_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering RV32I RVFI manifest, RV32I RVFI trace.
- RV32I RVFI manifest
- RV32I RVFI trace

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

- `REQ-SSPEC-UNIT`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `d4df0700fcf17a84c3ae41ddbafc6740cef35e5cd822cd7692fca4849e2542c3`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `d4df0700fcf17a84c3ae41ddbafc6740cef35e5cd822cd7692fca4849e2542c3`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `d4df0700fcf17a84c3ae41ddbafc6740cef35e5cd822cd7692fca4849e2542c3`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/unit/hardware/rv32i_rtl/rvfi_spec.spl
mirror: doc/06_spec/unit/hardware/rv32i_rtl/rvfi_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/unit/hardware/rv32i_rtl/rvfi_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/unit/hardware/rv32i_rtl/rvfi_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/unit/hardware/rv32i_rtl/rvfi_spec.spl:45:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'lists standard RVFI output ports' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/hardware/rv32i_rtl/rvfi_spec.spl:53:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'renders formal wrapper port comments' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/hardware/rv32i_rtl/rvfi_spec.spl:61:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'renders VHDL scalar and vector port types' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
