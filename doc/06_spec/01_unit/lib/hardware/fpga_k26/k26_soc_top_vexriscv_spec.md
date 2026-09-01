# K26 SoC Top VexRiscv-SMP Integration Specification

> Verifies AC-2: k26_soc_top wires VexRiscv-SMP .v + AXI-HP bridge + soc_rtl peripherals (CLINT, PLIC, UART16550). Tests that the generated VHDL/SV top-level text references VexRiscv-SMP, CLINT, PLIC, and UART.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 8 | 8 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# K26 SoC Top VexRiscv-SMP Integration Specification

Verifies AC-2: k26_soc_top wires VexRiscv-SMP .v + AXI-HP bridge + soc_rtl peripherals (CLINT, PLIC, UART16550). Tests that the generated VHDL/SV top-level text references VexRiscv-SMP, CLINT, PLIC, and UART.

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | opensource-riscv-rtl-simpleos |
| Category | Infrastructure |
| Difficulty | 3/5 |
| Status | Draft |
| Requirements | REQ-2 |
| Source | `test/01_unit/lib/hardware/fpga_k26/k26_soc_top_vexriscv_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Verifies AC-2: k26_soc_top wires VexRiscv-SMP .v + AXI-HP bridge +
soc_rtl peripherals (CLINT, PLIC, UART16550). Tests that the generated
VHDL/SV top-level text references VexRiscv-SMP, CLINT, PLIC, and UART.

Covers:
- AC-2 (SOC integration: core wired to CLINT+PLIC+UART16550)

## Scenarios

### K26VexRiscvSocConfig

#### AC-2: default config hart_count is 1

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- AC-2: default config hart_count is 1
   - Expected: cfg.hart_count equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("AC-2: default config hart_count is 1")
val cfg = default_soc_config()
expect(cfg.hart_count).to_equal(1)
```

</details>

#### AC-2: default config axi_data_width is 128

- AC-2: default config axi_data_width is 128
   - Expected: cfg.axi_data_width equals `128`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("AC-2: default config axi_data_width is 128")
val cfg = default_soc_config()
expect(cfg.axi_data_width).to_equal(128)
```

</details>

### K26 SoC Top VexRiscv-SMP Wiring

#### AC-2: generated text contains VexRiscv reference

- AC-2: generated text contains VexRiscv reference


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("AC-2: generated text contains VexRiscv reference")
val sv = soc_top_sv()
expect(sv).to_contain("VexRiscv")
```

</details>

#### AC-2: generated text references CLINT

- AC-2: generated text references CLINT


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("AC-2: generated text references CLINT")
val sv = soc_top_sv()
expect(sv).to_contain("clint")
```

</details>

#### AC-2: generated text references PLIC

- AC-2: generated text references PLIC


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("AC-2: generated text references PLIC")
val sv = soc_top_sv()
expect(sv).to_contain("plic")
```

</details>

#### AC-2: generated text references UART

- AC-2: generated text references UART


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("AC-2: generated text references UART")
val sv = soc_top_sv()
expect(sv).to_contain("uart")
```

</details>

#### AC-2: generated text references AXI HP bridge

- AC-2: generated text references AXI HP bridge


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("AC-2: generated text references AXI HP bridge")
val sv = soc_top_sv()
expect(sv).to_contain("HP0")
```

</details>

#### AC-2: generated text is non-empty

- AC-2: generated text is non-empty


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("AC-2: generated text is non-empty")
val sv = soc_top_sv()
val len = sv.length()
expect(len).to_be_greater_than(0)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 8 |
| Active scenarios | 8 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


## Related Documentation

- **Requirements:** `REQ-2`


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-LIB`
- `REQ-2`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `81bc7c3126cc81a7d635e99cc1f4d2937be5137c7fedf18feeac06204fba99ee`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `81bc7c3126cc81a7d635e99cc1f4d2937be5137c7fedf18feeac06204fba99ee`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `81bc7c3126cc81a7d635e99cc1f4d2937be5137c7fedf18feeac06204fba99ee`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **88/100**; effective score: **88/100**; blockers: **0**.

SSpec documentization score: 88/100
source: test/01_unit/lib/hardware/fpga_k26/k26_soc_top_vexriscv_spec.spl
mirror: doc/06_spec/01_unit/lib/hardware/fpga_k26/k26_soc_top_vexriscv_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=80
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/lib/hardware/fpga_k26/k26_soc_top_vexriscv_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/lib/hardware/fpga_k26/k26_soc_top_vexriscv_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/lib/hardware/fpga_k26/k26_soc_top_vexriscv_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-20): 2 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/lib/hardware/fpga_k26/k26_soc_top_vexriscv_spec.spl:58:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'AC-2: default config hart_count is 1' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/hardware/fpga_k26/k26_soc_top_vexriscv_spec.spl:64:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'AC-2: default config axi_data_width is 128' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/hardware/fpga_k26/k26_soc_top_vexriscv_spec.spl:76:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'AC-2: generated text contains VexRiscv reference' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
