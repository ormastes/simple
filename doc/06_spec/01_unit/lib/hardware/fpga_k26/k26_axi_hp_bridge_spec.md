# K26 AXI-HP Bridge Specification

> Verifies AC-2: AXI-HP bridge generates correct SystemVerilog for wiring VexRiscv-SMP AXI4 master to PS S_AXI_HP0 (128-bit burst DDR access). Tests that the generated SV text contains required module declarations, port names, and AXI4 signal names.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 10 | 10 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# K26 AXI-HP Bridge Specification

Verifies AC-2: AXI-HP bridge generates correct SystemVerilog for wiring VexRiscv-SMP AXI4 master to PS S_AXI_HP0 (128-bit burst DDR access). Tests that the generated SV text contains required module declarations, port names, and AXI4 signal names.

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | opensource-riscv-rtl-simpleos |
| Category | Infrastructure |
| Difficulty | 3/5 |
| Status | Draft |
| Requirements | REQ-2 |
| Source | `test/01_unit/lib/hardware/fpga_k26/k26_axi_hp_bridge_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Verifies AC-2: AXI-HP bridge generates correct SystemVerilog for wiring
VexRiscv-SMP AXI4 master to PS S_AXI_HP0 (128-bit burst DDR access).
Tests that the generated SV text contains required module declarations,
port names, and AXI4 signal names.

Covers:
- AC-2 (SOC integration: AXI-HP bridge for DDR access from PL core)

## Scenarios

### K26 AXI-HP Bridge SystemVerilog

#### AC-2: generated SV contains module declaration

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- AC-2: generated SV contains module declaration


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("AC-2: generated SV contains module declaration")
val sv = bridge_sv()
expect(sv).to_contain("module")
```

</details>

#### AC-2: generated SV contains endmodule

- AC-2: generated SV contains endmodule


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("AC-2: generated SV contains endmodule")
val sv = bridge_sv()
expect(sv).to_contain("endmodule")
```

</details>

#### AC-2: generated SV declares AXI AWADDR port

- AC-2: generated SV declares AXI AWADDR port


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("AC-2: generated SV declares AXI AWADDR port")
val sv = bridge_sv()
expect(sv).to_contain("AWADDR")
```

</details>

#### AC-2: generated SV declares AXI WDATA port

- AC-2: generated SV declares AXI WDATA port


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("AC-2: generated SV declares AXI WDATA port")
val sv = bridge_sv()
expect(sv).to_contain("WDATA")
```

</details>

#### AC-2: generated SV declares AXI ARADDR port

- AC-2: generated SV declares AXI ARADDR port


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("AC-2: generated SV declares AXI ARADDR port")
val sv = bridge_sv()
expect(sv).to_contain("ARADDR")
```

</details>

#### AC-2: generated SV declares AXI RDATA port

- AC-2: generated SV declares AXI RDATA port


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("AC-2: generated SV declares AXI RDATA port")
val sv = bridge_sv()
expect(sv).to_contain("RDATA")
```

</details>

#### AC-2: generated SV declares AXI AWBURST port

- AC-2: generated SV declares AXI AWBURST port


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("AC-2: generated SV declares AXI AWBURST port")
val sv = bridge_sv()
expect(sv).to_contain("AWBURST")
```

</details>

#### AC-2: generated SV references S_AXI_HP0

- AC-2: generated SV references S_AXI_HP0


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("AC-2: generated SV references S_AXI_HP0")
val sv = bridge_sv()
expect(sv).to_contain("HP0")
```

</details>

#### AC-2: generated SV is non-empty

- AC-2: generated SV is non-empty


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("AC-2: generated SV is non-empty")
val sv = bridge_sv()
val len = sv.length()
expect(len).to_be_greater_than(0)
```

</details>

#### AC-2: generated SV contains input/output port direction

- AC-2: generated SV contains input/output port direction


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("AC-2: generated SV contains input/output port direction")
val sv = bridge_sv()
expect(sv).to_contain("input")
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 10 |
| Active scenarios | 10 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


## Related Documentation

- **Requirements:** `REQ-2`


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-UNIT`
- `REQ-2`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `7c4812b81c535ac91a0486d4260601ab4d6ac1747c51d4b2fcdc4a3250660943`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `7c4812b81c535ac91a0486d4260601ab4d6ac1747c51d4b2fcdc4a3250660943`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `7c4812b81c535ac91a0486d4260601ab4d6ac1747c51d4b2fcdc4a3250660943`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/01_unit/lib/hardware/fpga_k26/k26_axi_hp_bridge_spec.spl
mirror: doc/06_spec/01_unit/lib/hardware/fpga_k26/k26_axi_hp_bridge_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/lib/hardware/fpga_k26/k26_axi_hp_bridge_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/lib/hardware/fpga_k26/k26_axi_hp_bridge_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/lib/hardware/fpga_k26/k26_axi_hp_bridge_spec.spl:47:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'AC-2: generated SV contains module declaration' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/hardware/fpga_k26/k26_axi_hp_bridge_spec.spl:53:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'AC-2: generated SV contains endmodule' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/hardware/fpga_k26/k26_axi_hp_bridge_spec.spl:59:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'AC-2: generated SV declares AXI AWADDR port' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
