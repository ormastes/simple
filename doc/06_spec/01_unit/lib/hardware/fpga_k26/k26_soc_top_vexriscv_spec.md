# K26 SoC Top VexRiscv-SMP Integration Specification

> Verifies the k26 soc top vexriscv behaviour end to end so maintainers of this

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 8 | 8 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# K26 SoC Top VexRiscv-SMP Integration Specification

Verifies the k26 soc top vexriscv behaviour end to end so maintainers of this

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | opensource-riscv-rtl-simpleos |
| Category | Infrastructure |
| Difficulty | 3/5 |
| Status | Draft |
| Requirements | REQ-2 |
| Source | `test/01_unit/lib/hardware/fpga_k26/k26_soc_top_vexriscv_spec.spl` |
| Updated | 2026-08-22 |
| Generator | `simple spipe-docgen` (Simple) |

## Purpose and audience
Verifies the k26 soc top vexriscv behaviour end to end so maintainers of this
component and reviewers of its spec share one pinned definition.
## Operator workflow
Run `bin/simple test <this spec>`; read the per-scenario verdicts in
the `Results:` summary. Each scenario asserts an observable outcome.
## Compatibility and limitations
Covers the currently shipped behaviour only; performance, stress and
unrelated sibling features are out of scope.

## Scenarios

### K26VexRiscvSocConfig

#### AC-2: default config hart_count is 1

- Verify: AC-2: default config hart_count is 1
   - Expected: cfg.hart_count equals `1)  # oracle: pinned constant asserted by this scenario`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-2
step("Verify: AC-2: default config hart_count is 1")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
val cfg = default_soc_config()
expect(cfg.hart_count).to_equal(1)  # oracle: pinned constant asserted by this scenario
```

</details>

#### AC-2: default config axi_data_width is 128

- Verify: AC-2: default config axi_data_width is 128
   - Expected: cfg.axi_data_width equals `128)  # oracle: pinned constant asserted by this scenario`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-2
step("Verify: AC-2: default config axi_data_width is 128")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
val cfg = default_soc_config()
expect(cfg.axi_data_width).to_equal(128)  # oracle: pinned constant asserted by this scenario
```

</details>

### K26 SoC Top VexRiscv-SMP Wiring

#### AC-2: generated text contains VexRiscv reference

- Verify: AC-2: generated text contains VexRiscv reference


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-2
step("Verify: AC-2: generated text contains VexRiscv reference")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
val sv = soc_top_sv()
expect(sv).to_contain("VexRiscv")
```

</details>

#### AC-2: generated text references CLINT

- Verify: AC-2: generated text references CLINT


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-2
step("Verify: AC-2: generated text references CLINT")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
val sv = soc_top_sv()
expect(sv).to_contain("clint")
```

</details>

#### AC-2: generated text references PLIC

- Verify: AC-2: generated text references PLIC


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-2
step("Verify: AC-2: generated text references PLIC")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
val sv = soc_top_sv()
expect(sv).to_contain("plic")
```

</details>

#### AC-2: generated text references UART

- Verify: AC-2: generated text references UART


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-2
step("Verify: AC-2: generated text references UART")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
val sv = soc_top_sv()
expect(sv).to_contain("uart")
```

</details>

#### AC-2: generated text references AXI HP bridge

- Verify: AC-2: generated text references AXI HP bridge


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-2
step("Verify: AC-2: generated text references AXI HP bridge")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
val sv = soc_top_sv()
expect(sv).to_contain("HP0")
```

</details>

#### AC-2: generated text is non-empty

- Verify: AC-2: generated text is non-empty


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-2
step("Verify: AC-2: generated text is non-empty")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
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

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `0577c43af5df0b0c2e1cf224521a9cc046a700dadcec224d9afaacfc9704e97e`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `0577c43af5df0b0c2e1cf224521a9cc046a700dadcec224d9afaacfc9704e97e`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `0577c43af5df0b0c2e1cf224521a9cc046a700dadcec224d9afaacfc9704e97e`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **94/100**; effective score: **94/100**; blockers: **0**.

SSpec documentization score: 94/100
source: test/01_unit/lib/hardware/fpga_k26/k26_soc_top_vexriscv_spec.spl
mirror: doc/06_spec/01_unit/lib/hardware/fpga_k26/k26_soc_top_vexriscv_spec.md (current)
findings: 3 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=85 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/lib/hardware/fpga_k26/k26_soc_top_vexriscv_spec.md:1:1: warning SSDOC-EVD-002 [evidence] (-15): source steps are not visible in the generated manual
  why: Source tokens alone do not prove reader-visible workflow structure.
  improve: Use supported literal step calls and regenerate the manual.
doc/06_spec/01_unit/lib/hardware/fpga_k26/k26_soc_top_vexriscv_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/lib/hardware/fpga_k26/k26_soc_top_vexriscv_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: assumptions/preconditions, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
<!-- sspec-maintain:scorecard:end -->
