# RISC-V Gen2 scalar ALU retire projection

> Checks that a high-bit ADDI instruction is emitted with a portable exact-width

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 1 | 1 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# RISC-V Gen2 scalar ALU retire projection

Checks that a high-bit ADDI instruction is emitted with a portable exact-width

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/03_system/app/hardware/feature/riscv_gen2_scalar_alu_projection_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

Checks that a high-bit ADDI instruction is emitted with a portable exact-width
VHDL literal and, when the required external analyzer is available, that GHDL
accepts the generated combinational projection. A missing analyzer produces a
visible conditional skip with its reason; it is never analysis evidence. This
is not architectural retirement or processor qualification.

## Scenarios

### strict scalar ALU retire projection VHDL

#### should analyze the RV32 ADDI 0xFFF08293 vector without INTEGER overflow when GHDL is available

- should analyze the RV32 ADDI 0xFFF08293 vector without INTEGER overflow when GHDL is available
   - Artifact capture: after_step
- Compile the exact RV32 high-bit ADDI scalar ALU retire projection
   - Artifact capture: after_step
   - Evidence: artifact verified by 1 expected check
   - Expected: emitted.is_success() is true
- Inspect the generated instruction literal for exact-width portable VHDL
   - Artifact capture: after_step
   - Evidence: artifact verified by 1 expected check
   - Expected: emitted.vhdl does not contain `to_unsigned(4293952147`
- Probe the required GHDL VHDL-2008 analyzer once
   - Artifact capture: after_step
- Write the generated scalar ALU VHDL artifact for external analysis
   - Artifact capture: after_step
   - Evidence: artifact verified by 1 expected check
   - Expected: rt_file_write_text("/tmp/riscv_gen2_scalar_addi_high_bit.vhd", emitted.vhdl) is true
- Analyze the generated VHDL artifact with GHDL VHDL-2008
   - Artifact capture: after_step
   - Evidence: artifact verified by 1 expected check
   - Expected: analyze_code equals `0`
- Record the visible skip and preserve the emitted-VHDL-only evidence boundary
   - Artifact capture: after_step


<details>
<summary>Executable SSpec</summary>

Runnable source: 26 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should analyze the RV32 ADDI 0xFFF08293 vector without INTEGER overflow when GHDL is available")
step("Compile the exact RV32 high-bit ADDI scalar ALU retire projection")
val emitted = compile_strict_riscv_scalar_alu_retire_projection_product(
    "scalar_addi_high_bit_rv32", CoreConfig.rv32(), 0xFFF08293)
expect(emitted.is_success()).to_equal(true)
step("Inspect the generated instruction literal for exact-width portable VHDL")
expect(emitted.vhdl).to_contain(
    "constant instruction : std_logic_vector(31 downto 0) := \"11111111111100001000001010010011\";")
expect(emitted.vhdl.contains("to_unsigned(4293952147")).to_equal(false)
step("Probe the required GHDL VHDL-2008 analyzer once")
val (_version_stdout, _version_stderr, version_code) = rt_process_run("ghdl", ["--version"])
if version_code == 0:
    step("Write the generated scalar ALU VHDL artifact for external analysis")
    expect(rt_file_write_text("/tmp/riscv_gen2_scalar_addi_high_bit.vhd", emitted.vhdl)).to_equal(true)
    step("Analyze the generated VHDL artifact with GHDL VHDL-2008")
    val (_stdout, _stderr, analyze_code) = rt_process_run("ghdl",
        ["-a", "--std=08", "/tmp/riscv_gen2_scalar_addi_high_bit.vhd"])
    expect(analyze_code).to_equal(0)
else:
    val reason = "ghdl --version returned exit code " + version_code.to_text() +
        "; GHDL VHDL-2008 analysis did not run on this host"
    skip("GHDL VHDL-2008 analyzer unavailable", reason)
    step("Record the visible skip and preserve the emitted-VHDL-only evidence boundary")
    print "[riscv_gen2_scalar_alu_projection_spec] SKIP reason=" + reason
    expect(reason).to_contain("ghdl --version returned exit code")
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 1 |
| Active scenarios | 1 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-SYSTEM`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `88a415eb6c716847a1dcb30c3327abdf12be2c84a87b443b82e44060e9ada566`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `88a415eb6c716847a1dcb30c3327abdf12be2c84a87b443b82e44060e9ada566`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `88a415eb6c716847a1dcb30c3327abdf12be2c84a87b443b82e44060e9ada566`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/03_system/app/hardware/feature/riscv_gen2_scalar_alu_projection_spec.spl
mirror: doc/06_spec/03_system/app/hardware/feature/riscv_gen2_scalar_alu_projection_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=95 oracle=90
  traceability=100 evidence=90 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/03_system/app/hardware/feature/riscv_gen2_scalar_alu_projection_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/app/hardware/feature/riscv_gen2_scalar_alu_projection_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/app/hardware/feature/riscv_gen2_scalar_alu_projection_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-10): 1 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/03_system/app/hardware/feature/riscv_gen2_scalar_alu_projection_spec.spl:30:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should analyze the RV32 ADDI 0xFFF08293 vector without INTEGER overflow when GHDL is available' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/03_system/app/hardware/feature/riscv_gen2_scalar_alu_projection_spec.spl:30:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should analyze the RV32 ADDI 0xFFF08293 vector without INTEGER overflow when GHDL is available' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
