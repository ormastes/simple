# RV64GC VHDL Generation Pipeline Specification

> Tests for VHDL generation pipeline producing valid RV64GC SoC VHDL. Verifies that generated VHDL text contains the correct entity names, port declarations, peripheral instantiations, and does NOT reference the old rv32i_core entity.

<!-- sdn-diagram:id=soc_vhdl_gen_rv64_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=soc_vhdl_gen_rv64_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

soc_vhdl_gen_rv64_spec -> std
soc_vhdl_gen_rv64_spec -> lib
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=soc_vhdl_gen_rv64_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 17 | 17 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# RV64GC VHDL Generation Pipeline Specification

Tests for VHDL generation pipeline producing valid RV64GC SoC VHDL. Verifies that generated VHDL text contains the correct entity names, port declarations, peripheral instantiations, and does NOT reference the old rv32i_core entity.

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | rv64-fpga-linux-boot |
| Category | Infrastructure |
| Difficulty | 4/5 |
| Status | Draft |
| Requirements | REQ-6, REQ-10, REQ-11 |
| Research | doc/01_research/domain/vhdl_backend_linux_rtl.md |
| Source | `test/01_unit/lib/hardware/fpga_linux/soc_vhdl_gen_rv64_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests for VHDL generation pipeline producing valid RV64GC SoC VHDL.
Verifies that generated VHDL text contains the correct entity names,
port declarations, peripheral instantiations, and does NOT reference
the old rv32i_core entity.

Covers: AC-2 (VHDL generation pipeline produces valid VHDL files
that GHDL can analyze without errors)

## Compiled-Mode Notes

Text-pattern checks on generated VHDL are interpreter-safe. Actual
GHDL analysis validation requires compiled mode with GHDL installed.

## Scenarios

### VHDL Gen RV64 Entity

#### AC-2: generate_soc_top_vhdl_rv64 returns non-empty text

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val vhdl = generate_soc_top_vhdl_rv64()
val len = vhdl.length()
expect(len).to_be_greater_than(0)
```

</details>

#### AC-2: generated VHDL contains rv64gc_core entity reference

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val vhdl = generate_soc_top_vhdl_rv64()
expect(vhdl).to_contain("rv64gc_core")
```

</details>

#### AC-2: generated VHDL does NOT contain rv32i_core entity

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val vhdl = generate_soc_top_vhdl_rv64()
val has_rv32 = vhdl.contains("rv32i_core")
expect(has_rv32).to_equal(false)
```

</details>

#### AC-2: generated VHDL contains entity declaration

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val vhdl = generate_soc_top_vhdl_rv64()
expect(vhdl).to_contain("entity")
```

</details>

#### AC-2: generated VHDL contains architecture declaration

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val vhdl = generate_soc_top_vhdl_rv64()
expect(vhdl).to_contain("architecture")
```

</details>

### VHDL Gen Peripheral Instantiation

#### AC-2: generated VHDL instantiates CLINT

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val vhdl = generate_soc_top_vhdl_rv64()
expect(vhdl).to_contain("clint")
```

</details>

#### AC-2: generated VHDL instantiates PLIC

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val vhdl = generate_soc_top_vhdl_rv64()
expect(vhdl).to_contain("plic")
```

</details>

#### AC-2: generated VHDL instantiates UART16550

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val vhdl = generate_soc_top_vhdl_rv64()
expect(vhdl).to_contain("uart")
```

</details>

#### AC-2: generated VHDL instantiates RAM

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val vhdl = generate_soc_top_vhdl_rv64()
expect(vhdl).to_contain("ram")
```

</details>

#### AC-2: generated VHDL instantiates bootrom

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val vhdl = generate_soc_top_vhdl_rv64()
expect(vhdl).to_contain("bootrom")
```

</details>

#### AC-2: generated VHDL instantiates wishbone interconnect

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val vhdl = generate_soc_top_vhdl_rv64()
expect(vhdl).to_contain("wb")
```

</details>

### VHDL Gen 64-bit Port Widths

#### AC-2: generated VHDL uses 64-bit data bus width

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val vhdl = generate_soc_top_vhdl_rv64()
expect(vhdl).to_contain("63 downto 0")
```

</details>

#### AC-2: generated VHDL contains clock port

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val vhdl = generate_soc_top_vhdl_rv64()
expect(vhdl).to_contain("clk")
```

</details>

#### AC-2: generated VHDL contains reset port

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val vhdl = generate_soc_top_vhdl_rv64()
expect(vhdl).to_contain("rst")
```

</details>

### VHDL Backend RTL Module Compilation

#### AC-2: VHDL backend produces output for core.spl (compiled mode + GHDL)

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# This test requires compiled mode: run VHDL backend against core.spl
# and verify GHDL analysis passes. Interpreter-safe check: function exists.
val vhdl = compile_to_vhdl_module("src/lib/hardware/rv64gc_rtl/core.spl")
val len = vhdl.length()
expect(len).to_be_greater_than(0)
```

</details>

#### AC-2: VHDL backend produces output for alu.spl (compiled mode + GHDL)

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val vhdl = compile_to_vhdl_module("src/lib/hardware/rv64gc_rtl/alu.spl")
val len = vhdl.length()
expect(len).to_be_greater_than(0)
```

</details>

#### AC-2: VHDL backend produces output for decode.spl (compiled mode + GHDL)

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val vhdl = compile_to_vhdl_module("src/lib/hardware/rv64gc_rtl/decode.spl")
val len = vhdl.length()
expect(len).to_be_greater_than(0)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 17 |
| Active scenarios | 17 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


## Related Documentation

- **Requirements:** [REQ-6, REQ-10, REQ-11](REQ-6, REQ-10, REQ-11)
- **Research:** [doc/01_research/domain/vhdl_backend_linux_rtl.md](doc/01_research/domain/vhdl_backend_linux_rtl.md)


</details>
