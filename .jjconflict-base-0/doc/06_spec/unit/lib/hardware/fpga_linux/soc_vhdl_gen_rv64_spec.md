# RV64GC VHDL Generation Pipeline Specification

> Tests for VHDL generation pipeline producing valid RV64GC SoC VHDL. Verifies that generated VHDL text contains the correct entity names, port declarations, peripheral instantiations, and does NOT reference the old rv32i_core entity.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 14 | 14 | 0 | 0 |

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
| Source | `test/unit/lib/hardware/fpga_linux/soc_vhdl_gen_rv64_spec.spl` |
| Updated | 2026-08-26 |
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

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-6
# @req REQ-10
# @req REQ-11
```

</details>

#### AC-2: generated VHDL contains rv64gc_core entity reference

- AC-2: generated VHDL contains rv64gc_core entity reference


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("AC-2: generated VHDL contains rv64gc_core entity reference")
val vhdl = generate_soc_top_vhdl_rv64()
expect(vhdl).to_contain("rv64gc_core")
```

</details>

#### AC-2: generated VHDL does NOT contain rv32i_core entity

- AC-2: generated VHDL does NOT contain rv32i_core entity
   - Expected: has_rv32 is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("AC-2: generated VHDL does NOT contain rv32i_core entity")
val vhdl = generate_soc_top_vhdl_rv64()
val has_rv32 = vhdl.contains("rv32i_core")
expect(has_rv32).to_equal(false)
```

</details>

#### AC-2: generated VHDL contains entity declaration

- AC-2: generated VHDL contains entity declaration


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("AC-2: generated VHDL contains entity declaration")
val vhdl = generate_soc_top_vhdl_rv64()
expect(vhdl).to_contain("entity")
```

</details>

#### AC-2: generated VHDL contains architecture declaration

- AC-2: generated VHDL contains architecture declaration


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("AC-2: generated VHDL contains architecture declaration")
val vhdl = generate_soc_top_vhdl_rv64()
expect(vhdl).to_contain("architecture")
```

</details>

### VHDL Gen Peripheral Instantiation

#### AC-2: generated VHDL instantiates CLINT

- AC-2: generated VHDL instantiates CLINT


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("AC-2: generated VHDL instantiates CLINT")
val vhdl = generate_soc_top_vhdl_rv64()
expect(vhdl).to_contain("clint")
```

</details>

#### AC-2: generated VHDL instantiates PLIC

- AC-2: generated VHDL instantiates PLIC


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("AC-2: generated VHDL instantiates PLIC")
val vhdl = generate_soc_top_vhdl_rv64()
expect(vhdl).to_contain("plic")
```

</details>

#### AC-2: generated VHDL instantiates UART16550

- AC-2: generated VHDL instantiates UART16550


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("AC-2: generated VHDL instantiates UART16550")
val vhdl = generate_soc_top_vhdl_rv64()
expect(vhdl).to_contain("uart")
```

</details>

#### AC-2: generated VHDL instantiates RAM

- AC-2: generated VHDL instantiates RAM


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("AC-2: generated VHDL instantiates RAM")
val vhdl = generate_soc_top_vhdl_rv64()
expect(vhdl).to_contain("ram")
```

</details>

#### AC-2: generated VHDL instantiates bootrom

- AC-2: generated VHDL instantiates bootrom


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("AC-2: generated VHDL instantiates bootrom")
val vhdl = generate_soc_top_vhdl_rv64()
expect(vhdl).to_contain("bootrom")
```

</details>

#### AC-2: generated VHDL instantiates wishbone interconnect

- AC-2: generated VHDL instantiates wishbone interconnect


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("AC-2: generated VHDL instantiates wishbone interconnect")
val vhdl = generate_soc_top_vhdl_rv64()
expect(vhdl).to_contain("wb")
```

</details>

### VHDL Gen 64-bit Port Widths

#### AC-2: generated VHDL uses 64-bit data bus width

- AC-2: generated VHDL uses 64-bit data bus width


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("AC-2: generated VHDL uses 64-bit data bus width")
val vhdl = generate_soc_top_vhdl_rv64()
expect(vhdl).to_contain("63 downto 0")
```

</details>

#### AC-2: generated VHDL contains clock port

- AC-2: generated VHDL contains clock port


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("AC-2: generated VHDL contains clock port")
val vhdl = generate_soc_top_vhdl_rv64()
expect(vhdl).to_contain("clk")
```

</details>

#### AC-2: generated VHDL contains reset port

- AC-2: generated VHDL contains reset port


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("AC-2: generated VHDL contains reset port")
val vhdl = generate_soc_top_vhdl_rv64()
expect(vhdl).to_contain("rst")
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 14 |
| Active scenarios | 14 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


## Related Documentation

- **Requirements:** `REQ-6, REQ-10, REQ-11`
- **Research:** `doc/01_research/domain/vhdl_backend_linux_rtl.md`


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-UNIT`
- `REQ-6`
- `REQ-10`
- `REQ-11`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `9e107ea6142a217b93798cf464ca49b3a0250ea2a4668dc45c9bd335f0404359`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `9e107ea6142a217b93798cf464ca49b3a0250ea2a4668dc45c9bd335f0404359`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `9e107ea6142a217b93798cf464ca49b3a0250ea2a4668dc45c9bd335f0404359`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **91/100**; effective score: **91/100**; blockers: **0**.

SSpec documentization score: 91/100
source: test/unit/lib/hardware/fpga_linux/soc_vhdl_gen_rv64_spec.spl
mirror: doc/06_spec/unit/lib/hardware/fpga_linux/soc_vhdl_gen_rv64_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=90 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/unit/lib/hardware/fpga_linux/soc_vhdl_gen_rv64_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/unit/lib/hardware/fpga_linux/soc_vhdl_gen_rv64_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/unit/lib/hardware/fpga_linux/soc_vhdl_gen_rv64_spec.spl:46:1: warning SSDOC-BEH-001 [structure] (-10): scenario 'AC-2: generate_soc_top_vhdl_rv64 returns non-empty text' has no visible step flow
  why: Ordered visible actions make the manual operable.
  improve: Add ordered step("...") calls for meaningful actions.
test/unit/lib/hardware/fpga_linux/soc_vhdl_gen_rv64_spec.spl:59:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'AC-2: generated VHDL contains rv64gc_core entity reference' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/lib/hardware/fpga_linux/soc_vhdl_gen_rv64_spec.spl:65:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'AC-2: generated VHDL does NOT contain rv32i_core entity' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/lib/hardware/fpga_linux/soc_vhdl_gen_rv64_spec.spl:72:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'AC-2: generated VHDL contains entity declaration' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
