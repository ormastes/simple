# RV64GC VHDL Generation Pipeline Specification

> Verifies the soc vhdl gen rv64 behaviour end to end so maintainers of this

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 15 | 15 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# RV64GC VHDL Generation Pipeline Specification

Verifies the soc vhdl gen rv64 behaviour end to end so maintainers of this

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
| Updated | 2026-08-22 |
| Generator | `simple spipe-docgen` (Simple) |

## Purpose and audience
Verifies the soc vhdl gen rv64 behaviour end to end so maintainers of this
component and reviewers of its spec share one pinned definition.
## Operator workflow
Run `bin/simple test <this spec>`; read the per-scenario verdicts in
the `Results:` summary. Each scenario asserts an observable outcome.
## Compatibility and limitations
Covers the currently shipped behaviour only; performance, stress and
unrelated sibling features are out of scope.

## Scenarios

### VHDL Gen RV64 Entity

#### AC-2: generate_soc_top_vhdl_rv64 returns non-empty text

- Verify: AC-2: generate_soc_top_vhdl_rv64 returns non-empty text


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-6 REQ-10 REQ-11
step("Verify: AC-2: generate_soc_top_vhdl_rv64 returns non-empty text")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
val vhdl = generate_soc_top_vhdl_rv64()
val len = vhdl.length()
expect(len).to_be_greater_than(0)
```

</details>

#### AC-2: generated VHDL contains rv64gc_core entity reference

- Verify: AC-2: generated VHDL contains rv64gc_core entity reference


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-6 REQ-10 REQ-11
step("Verify: AC-2: generated VHDL contains rv64gc_core entity reference")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
val vhdl = generate_soc_top_vhdl_rv64()
expect(vhdl).to_contain("rv64gc_core")
```

</details>

#### AC-2: generated VHDL does NOT contain rv32i_core entity

- Verify: AC-2: generated VHDL does NOT contain rv32i_core entity
   - Expected: has_rv32 is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-6 REQ-10 REQ-11
step("Verify: AC-2: generated VHDL does NOT contain rv32i_core entity")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
val vhdl = generate_soc_top_vhdl_rv64()
val has_rv32 = vhdl.contains("rv32i_core")
expect(has_rv32).to_equal(false)
```

</details>

#### AC-2: generated VHDL contains entity declaration

- Verify: AC-2: generated VHDL contains entity declaration


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-6 REQ-10 REQ-11
step("Verify: AC-2: generated VHDL contains entity declaration")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
val vhdl = generate_soc_top_vhdl_rv64()
expect(vhdl).to_contain("entity")
```

</details>

#### AC-2: generated VHDL contains architecture declaration

- Verify: AC-2: generated VHDL contains architecture declaration


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-6 REQ-10 REQ-11
step("Verify: AC-2: generated VHDL contains architecture declaration")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
val vhdl = generate_soc_top_vhdl_rv64()
expect(vhdl).to_contain("architecture")
```

</details>

### VHDL Gen Peripheral Instantiation

#### AC-2: generated VHDL instantiates CLINT

- Verify: AC-2: generated VHDL instantiates CLINT


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-6 REQ-10 REQ-11
step("Verify: AC-2: generated VHDL instantiates CLINT")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
val vhdl = generate_soc_top_vhdl_rv64()
expect(vhdl).to_contain("clint")
```

</details>

#### AC-2: generated VHDL instantiates PLIC

- Verify: AC-2: generated VHDL instantiates PLIC


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-6 REQ-10 REQ-11
step("Verify: AC-2: generated VHDL instantiates PLIC")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
val vhdl = generate_soc_top_vhdl_rv64()
expect(vhdl).to_contain("plic")
```

</details>

#### AC-2: generated VHDL instantiates UART16550

- Verify: AC-2: generated VHDL instantiates UART16550


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-6 REQ-10 REQ-11
step("Verify: AC-2: generated VHDL instantiates UART16550")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
val vhdl = generate_soc_top_vhdl_rv64()
expect(vhdl).to_contain("uart")
```

</details>

#### AC-2: generated VHDL instantiates RAM

- Verify: AC-2: generated VHDL instantiates RAM


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-6 REQ-10 REQ-11
step("Verify: AC-2: generated VHDL instantiates RAM")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
val vhdl = generate_soc_top_vhdl_rv64()
expect(vhdl).to_contain("ram")
```

</details>

#### AC-2: generated VHDL instantiates bootrom

- Verify: AC-2: generated VHDL instantiates bootrom


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-6 REQ-10 REQ-11
step("Verify: AC-2: generated VHDL instantiates bootrom")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
val vhdl = generate_soc_top_vhdl_rv64()
expect(vhdl).to_contain("bootrom")
```

</details>

#### AC-2: generated VHDL instantiates wishbone interconnect

- Verify: AC-2: generated VHDL instantiates wishbone interconnect


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-6 REQ-10 REQ-11
step("Verify: AC-2: generated VHDL instantiates wishbone interconnect")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
val vhdl = generate_soc_top_vhdl_rv64()
expect(vhdl).to_contain("wb")
```

</details>

### VHDL Gen 64-bit Port Widths

#### AC-2: generated VHDL uses 64-bit data bus width

- Verify: AC-2: generated VHDL uses 64-bit data bus width


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-6 REQ-10 REQ-11
step("Verify: AC-2: generated VHDL uses 64-bit data bus width")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
val vhdl = generate_soc_top_vhdl_rv64()
expect(vhdl).to_contain("63 downto 0")
```

</details>

#### AC-2: generated VHDL contains clock port

- Verify: AC-2: generated VHDL contains clock port


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-6 REQ-10 REQ-11
step("Verify: AC-2: generated VHDL contains clock port")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
val vhdl = generate_soc_top_vhdl_rv64()
expect(vhdl).to_contain("clk")
```

</details>

#### AC-2: generated VHDL contains reset port

- Verify: AC-2: generated VHDL contains reset port


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-6 REQ-10 REQ-11
step("Verify: AC-2: generated VHDL contains reset port")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
val vhdl = generate_soc_top_vhdl_rv64()
expect(vhdl).to_contain("rst")
```

</details>

### VHDL Gen External DDR Boundary

#### routes only the canonical 128 MiB DDR window to external Wishbone

- Verify: routes only the canonical 128 MiB DDR window to external Wishbone
   - Expected: top does not contain `u_ram : entity work.ram`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-6 REQ-10 REQ-11
step("Verify: routes only the canonical 128 MiB DDR window to external Wishbone")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
val top = generate_soc_top_vhdl_rv64_external_ddr()
val interconnect = generate_wb_interconnect_vhdl_rv64()
expect(top).to_contain("entity soc_top_rv64_external_ddr is")
expect(top).to_contain("ddr_wb_adr_o : out std_logic_vector(63 downto 0)")
expect(top).to_contain("s4_dat => ddr_wb_dat_i")
expect(top.contains("u_ram : entity work.ram")).to_equal(false)
expect(interconnect).to_contain("m_adr(63 downto 32) = x\"00000000\"")
expect(interconnect).to_contain("m_adr(31 downto 27) = \"10000\"")
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 15 |
| Active scenarios | 15 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


## Related Documentation

- **Requirements:** `REQ-6, REQ-10, REQ-11`
- **Research:** `doc/01_research/domain/vhdl_backend_linux_rtl.md`


</details>

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `9db2b05e99f6395efe188b0158b2ff8bbdd2edc2f2b337000d583aeaf9edf105`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `9db2b05e99f6395efe188b0158b2ff8bbdd2edc2f2b337000d583aeaf9edf105`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `9db2b05e99f6395efe188b0158b2ff8bbdd2edc2f2b337000d583aeaf9edf105`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **94/100**; effective score: **94/100**; blockers: **0**.

SSpec documentization score: 94/100
source: test/01_unit/lib/hardware/fpga_linux/soc_vhdl_gen_rv64_spec.spl
mirror: doc/06_spec/01_unit/lib/hardware/fpga_linux/soc_vhdl_gen_rv64_spec.md (current)
findings: 3 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=85 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/lib/hardware/fpga_linux/soc_vhdl_gen_rv64_spec.md:1:1: warning SSDOC-EVD-002 [evidence] (-15): source steps are not visible in the generated manual
  why: Source tokens alone do not prove reader-visible workflow structure.
  improve: Use supported literal step calls and regenerate the manual.
doc/06_spec/01_unit/lib/hardware/fpga_linux/soc_vhdl_gen_rv64_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/lib/hardware/fpga_linux/soc_vhdl_gen_rv64_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: assumptions/preconditions, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
<!-- sspec-maintain:scorecard:end -->
