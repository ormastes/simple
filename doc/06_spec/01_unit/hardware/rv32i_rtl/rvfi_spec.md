# Rvfi Specification

> Tests covering RV32I RVFI manifest, RV32I RVFI trace.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 12 | 12 | 0 | 0 |

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

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("lists standard RVFI output ports")
val ports = rvfi_port_manifest()
expect ports.len() == 21
expect ports[0].name == "rvfi_valid"
expect ports[2].name == "rvfi_insn"
expect ports[4].name == "rvfi_halt"
expect ports[7].name == "rvfi_ixl"
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

#### reports missing RVFI ports before formal flow runs

- reports missing RVFI ports before formal flow runs


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("reports missing RVFI ports before formal flow runs")
val entity = "entity rv32i_core is port (clk : in std_logic; reset_n : in std_logic); end entity;"
val missing = rvfi_missing_vhdl_ports(entity)
expect missing.len() == 21
expect missing[0] == "rvfi_valid"
val readiness = rvfi_formal_readiness("rv32i_core", entity)
check(not readiness.ready)
check(readiness.message.contains("missing 21 RVFI ports"))
check(rvfi_render_formal_readiness(readiness).contains("- rvfi_mem_wdata"))
```

</details>

#### accepts a VHDL entity with the full RVFI manifest

- accepts a VHDL entity with the full RVFI manifest


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("accepts a VHDL entity with the full RVFI manifest")
val wrapper = rvfi_formal_wrapper_vhdl("rv32i_core_rvfi", "rv32i_core")
val readiness = rvfi_formal_readiness("rv32i_core_rvfi", wrapper)
check(readiness.ready)
expect readiness.missing_ports.len() == 0
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

#### allows simultaneous read and write masks only for AMO

- allows simultaneous read and write masks only for AMO


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("allows simultaneous read and write masks only for AMO")
var amo = rvfi_trace_from_snapshot(rvfi_enabled_config(0), 0, snapshot_sample())
amo.rvfi_insn = 0x0020A1AF
amo.rvfi_mem_rmask = 0xF
amo.rvfi_mem_wmask = 0xF
expect rvfi_check_traces([amo]).len() == 0
amo.rvfi_insn = 0x00202023
expect rvfi_check_traces([amo]).len() == 1
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
| Source | `test/01_unit/hardware/rv32i_rtl/rvfi_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering RV32I RVFI manifest, RV32I RVFI trace.
- RV32I RVFI manifest
- RV32I RVFI trace

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

- `REQ-SSPEC-UNIT`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `6f2a6bd81bce9e433a14a37ca85ab53d24608dba754c197edb793690ebb56c19`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `6f2a6bd81bce9e433a14a37ca85ab53d24608dba754c197edb793690ebb56c19`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `6f2a6bd81bce9e433a14a37ca85ab53d24608dba754c197edb793690ebb56c19`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/01_unit/hardware/rv32i_rtl/rvfi_spec.spl
mirror: doc/06_spec/01_unit/hardware/rv32i_rtl/rvfi_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/hardware/rv32i_rtl/rvfi_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/hardware/rv32i_rtl/rvfi_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/hardware/rv32i_rtl/rvfi_spec.spl:47:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'lists standard RVFI output ports' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/hardware/rv32i_rtl/rvfi_spec.spl:57:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'renders formal wrapper port comments' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/hardware/rv32i_rtl/rvfi_spec.spl:65:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'renders VHDL scalar and vector port types' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
