# RISC-V Gen2 scalar control projection

> Verifies the riscv gen2 scalar control projection behaviour end to end so maintainers of this

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 1 | 1 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# RISC-V Gen2 scalar control projection

Verifies the riscv gen2 scalar control projection behaviour end to end so maintainers of this

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/03_system/app/hardware/feature/riscv_gen2_scalar_control_projection_spec.spl` |
| Updated | 2026-08-22 |
| Generator | `simple spipe-docgen` (Simple) |

## Purpose and audience
Verifies the riscv gen2 scalar control projection behaviour end to end so maintainers of this
component and reviewers of its spec share one pinned definition.
## Operator workflow
Run `bin/simple test <this spec>`; read the per-scenario verdicts in
the `Results:` summary. Each scenario asserts an observable outcome.
## Compatibility and limitations
Covers the currently shipped behaviour only; performance, stress and
unrelated sibling features are out of scope.

## Scenarios

### strict scalar control projection VHDL

#### should analyze concrete RV32 and RV64 JALR bit-clear graphs when GHDL is available

- Verify: should analyze concrete RV32 and RV64 JALR bit-clear graphs when GHDL is available
- Compile the exact RV32 and RV64 JALR bit-clear projection products
   - Expected: rv32.is_success() is true
   - Expected: rv64.is_success() is true
- Probe the required GHDL VHDL-2008 analyzer once
- Write the generated RV32 and RV64 VHDL artifacts for external analysis
   - Expected: rt_file_write_text("/tmp/riscv_scalar_control_rv32.vhd", rv32.vhdl) is true
   - Expected: rt_file_write_text("/tmp/riscv_scalar_control_rv64.vhd", rv64.vhdl) is true
- Analyze both generated VHDL artifacts with GHDL VHDL-2008
   - Expected: code32 equals `0)  # oracle: pinned constant asserted by this scenario`
   - Expected: code64 equals `0)  # oracle: pinned constant asserted by this scenario`
- Record the named GHDL-unavailable skip and preserve host-only projection evidence


<details>
<summary>Executable SSpec</summary>

Runnable source: 26 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-G2-001 REQ-G2-002 REQ-G2-003
step("Verify: should analyze concrete RV32 and RV64 JALR bit-clear graphs when GHDL is available")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
step("Compile the exact RV32 and RV64 JALR bit-clear projection products")
val rv32 = compile_strict_riscv_scalar_control_projection_product(
    "scalar_jalr_projection_rv32", CoreConfig.rv32(), 0xFFF082E7)
val rv64 = compile_strict_riscv_scalar_control_projection_product(
    "scalar_jalr_projection_rv64", CoreConfig.rv64(), 0xFFF082E7)
expect(rv32.is_success()).to_equal(true)
expect(rv64.is_success()).to_equal(true)
expect(rv32.vhdl).to_contain("control_target <= raw_target and target_mask;")
expect(rv64.vhdl).to_contain("control_target <= raw_target and target_mask;")
step("Probe the required GHDL VHDL-2008 analyzer once")
val (_version_stdout, _version_stderr, version_code) = rt_process_run("ghdl", ["--version"])
if version_code == 0:
    step("Write the generated RV32 and RV64 VHDL artifacts for external analysis")
    expect(rt_file_write_text("/tmp/riscv_scalar_control_rv32.vhd", rv32.vhdl)).to_equal(true)
    expect(rt_file_write_text("/tmp/riscv_scalar_control_rv64.vhd", rv64.vhdl)).to_equal(true)
    step("Analyze both generated VHDL artifacts with GHDL VHDL-2008")
    val (_out32, _err32, code32) = rt_process_run("ghdl", ["-a", "--std=08", "/tmp/riscv_scalar_control_rv32.vhd"])
    val (_out64, _err64, code64) = rt_process_run("ghdl", ["-a", "--std=08", "/tmp/riscv_scalar_control_rv64.vhd"])
    expect(code32).to_equal(0)  # oracle: pinned constant asserted by this scenario
    expect(code64).to_equal(0)  # oracle: pinned constant asserted by this scenario
else:
    step("Record the named GHDL-unavailable skip and preserve host-only projection evidence")
    print "SKIP: GHDL VHDL-2008 analyzer unavailable (ghdl --version exit " + version_code.to_text() + ")"
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

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `d46227034d4a6fca33a031dd32e47468c82ef45453cff935ad2eb596aa668dc1`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `d46227034d4a6fca33a031dd32e47468c82ef45453cff935ad2eb596aa668dc1`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `d46227034d4a6fca33a031dd32e47468c82ef45453cff935ad2eb596aa668dc1`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **94/100**; effective score: **94/100**; blockers: **0**.

SSpec documentization score: 94/100
source: test/03_system/app/hardware/feature/riscv_gen2_scalar_control_projection_spec.spl
mirror: doc/06_spec/03_system/app/hardware/feature/riscv_gen2_scalar_control_projection_spec.md (current)
findings: 4 blockers: 0
  narrative=100 structure=95 oracle=100
  traceability=100 evidence=85 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/03_system/app/hardware/feature/riscv_gen2_scalar_control_projection_spec.md:1:1: warning SSDOC-EVD-002 [evidence] (-15): source steps are not visible in the generated manual
  why: Source tokens alone do not prove reader-visible workflow structure.
  improve: Use supported literal step calls and regenerate the manual.
doc/06_spec/03_system/app/hardware/feature/riscv_gen2_scalar_control_projection_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/app/hardware/feature/riscv_gen2_scalar_control_projection_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: assumptions/preconditions, traceability, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/app/hardware/feature/riscv_gen2_scalar_control_projection_spec.spl:36:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should analyze concrete RV32 and RV64 JALR bit-clear graphs when GHDL is available' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
<!-- sspec-maintain:scorecard:end -->
