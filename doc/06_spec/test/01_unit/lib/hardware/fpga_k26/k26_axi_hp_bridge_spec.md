# K26 AXI-HP Bridge Specification

> Verifies AC-2: AXI-HP bridge generates correct SystemVerilog for wiring VexRiscv-SMP AXI4 master to PS S_AXI_HP0 (128-bit burst DDR access). Tests that the generated SV text contains required module declarations, port names, and AXI4 signal names.

<!-- sdn-diagram:id=k26_axi_hp_bridge_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=k26_axi_hp_bridge_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

k26_axi_hp_bridge_spec -> std
k26_axi_hp_bridge_spec -> lib
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=k26_axi_hp_bridge_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

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
| Updated | 2026-06-01 |
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

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val sv = bridge_sv()
expect(sv).to_contain("module")
```

</details>

#### AC-2: generated SV contains endmodule

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val sv = bridge_sv()
expect(sv).to_contain("endmodule")
```

</details>

#### AC-2: generated SV declares AXI AWADDR port

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val sv = bridge_sv()
expect(sv).to_contain("AWADDR")
```

</details>

#### AC-2: generated SV declares AXI WDATA port

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val sv = bridge_sv()
expect(sv).to_contain("WDATA")
```

</details>

#### AC-2: generated SV declares AXI ARADDR port

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val sv = bridge_sv()
expect(sv).to_contain("ARADDR")
```

</details>

#### AC-2: generated SV declares AXI RDATA port

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val sv = bridge_sv()
expect(sv).to_contain("RDATA")
```

</details>

#### AC-2: generated SV declares AXI AWBURST port

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val sv = bridge_sv()
expect(sv).to_contain("AWBURST")
```

</details>

#### AC-2: generated SV references S_AXI_HP0

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val sv = bridge_sv()
expect(sv).to_contain("HP0")
```

</details>

#### AC-2: generated SV is non-empty

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val sv = bridge_sv()
val len = sv.length()
expect(len).to_be_greater_than(0)
```

</details>

#### AC-2: generated SV contains input/output port direction

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

- **Requirements:** [REQ-2](REQ-2)


</details>
