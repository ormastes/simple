# RISC-V Gen2 scalar control projection

> This scenario emits concrete RV32 and RV64 JALR bit-clear projections. When

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 1 | 1 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# RISC-V Gen2 scalar control projection

This scenario emits concrete RV32 and RV64 JALR bit-clear projections. When

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/03_system/app/hardware/feature/riscv_gen2_scalar_control_projection_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

This scenario emits concrete RV32 and RV64 JALR bit-clear projections. When
the external GHDL VHDL-2008 analyzer is installed, it analyzes both generated
artifacts. This is stateless projection evidence, not processor qualification.

## Scenarios

### strict scalar control projection VHDL

#### should analyze concrete RV32 and RV64 JALR bit-clear graphs when GHDL is available

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- should analyze concrete RV32 and RV64 JALR bit-clear graphs when GHDL is available
- Compile the exact RV32 and RV64 JALR bit-clear projection products
   - Expected: rv32.is_success() is true
   - Expected: rv64.is_success() is true
- Probe the required GHDL VHDL-2008 analyzer once
- Write the generated RV32 and RV64 VHDL artifacts for external analysis
   - Expected: rt_file_write_text("/tmp/riscv_scalar_control_rv32.vhd", rv32.vhdl) is true
   - Expected: rt_file_write_text("/tmp/riscv_scalar_control_rv64.vhd", rv64.vhdl) is true
- Analyze both generated VHDL artifacts with GHDL VHDL-2008
   - Expected: code32 equals `0`
   - Expected: code64 equals `0`
- Record the named GHDL-unavailable skip and preserve host-only projection evidence


<details>
<summary>Executable SSpec</summary>

Runnable source: 25 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should analyze concrete RV32 and RV64 JALR bit-clear graphs when GHDL is available")
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
    expect(code32).to_equal(0)
    expect(code64).to_equal(0)
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

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-SYSTEM`
- `REQ-G2-001`
- `REQ-G2-002`
- `REQ-G2-003`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `893c0473276af31d85fb2e8c4e1c64f0b68c3d3ee21751dd767c6c98e34e6042`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `893c0473276af31d85fb2e8c4e1c64f0b68c3d3ee21751dd767c6c98e34e6042`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `893c0473276af31d85fb2e8c4e1c64f0b68c3d3ee21751dd767c6c98e34e6042`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **84/100**; effective score: **49/100**; blockers: **1**.

SSpec documentization score: 49/100
source: test/03_system/app/hardware/feature/riscv_gen2_scalar_control_projection_spec.spl
mirror: doc/06_spec/03_system/app/hardware/feature/riscv_gen2_scalar_control_projection_spec.md (current)
findings: 6 blockers: 1
  narrative=100 structure=95 oracle=80
  traceability=60 evidence=90 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
  raw=84; blocker cap makes effective=49
doc/06_spec/03_system/app/hardware/feature/riscv_gen2_scalar_control_projection_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/app/hardware/feature/riscv_gen2_scalar_control_projection_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/app/hardware/feature/riscv_gen2_scalar_control_projection_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-20): 2 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/03_system/app/hardware/feature/riscv_gen2_scalar_control_projection_spec.spl:1:1: blocker SSDOC-TRC-003 [traceability] (-40): 3 declared requirement(s) have no scenario binding
  why: A requirement list without scenario evidence is inventory, not traceability.
  improve: Bind the stable requirement ID inside its executable scenario or explicit blocked case.
test/03_system/app/hardware/feature/riscv_gen2_scalar_control_projection_spec.spl:26:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should analyze concrete RV32 and RV64 JALR bit-clear graphs when GHDL is available' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/03_system/app/hardware/feature/riscv_gen2_scalar_control_projection_spec.spl:26:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should analyze concrete RV32 and RV64 JALR bit-clear graphs when GHDL is available' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
