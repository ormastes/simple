# Hwir Riscv Scalar Execution Specification

> Tests covering shared emitted Gen2 scalar ALU retirement slice.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 4 | 4 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Hwir Riscv Scalar Execution Specification

## Scenarios

### shared emitted Gen2 scalar ALU retirement slice

#### should monomorphize the same base-I ALU rows for RV32 and RV64

- should monomorphize the same base-I ALU rows for RV32 and RV64
- Build each bounded base-I ALU row for concrete RV32 and RV64 configurations


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("should monomorphize the same base-I ALU rows for RV32 and RV64")
step("Build each bounded base-I ALU row for concrete RV32 and RV64 configurations")
val instructions: [u32] = [0x002082B3, 0x402082B3, 0x0020F2B3,
    0x0020E2B3, 0x0020C2B3, 0xFFF08293]
val operations = ["add", "sub", "and", "or", "xor", "add"]
var index = 0
while index < instructions.len():
    expect_scalar_shape(CoreConfig.rv32(), instructions[index], operations[index])
    expect_scalar_shape(CoreConfig.rv64(), instructions[index], operations[index])
    index = index + 1
```

</details>

#### should emit strict concrete-width VHDL and exact retirement outputs

- should emit strict concrete-width VHDL and exact retirement outputs
- Compile concrete RV32 ADD and RV64 SUB retirement-projection products
   - Expected: rv32.is_success() is true
   - Expected: rv64.is_success() is true
   - Expected: rv32.route equals `hwir-gen2-scalar-alu-retire-projection-v1`
   - Expected: rv64.route equals `hwir-gen2-scalar-alu-retire-projection-v1`
   - Expected: rv32.vhdl does not contain `"xlen =") or rv32.vhdl`
   - Expected: rv64.vhdl does not contain `"xlen =") or rv64.vhdl`


<details>
<summary>Executable SSpec</summary>

Runnable source: 20 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("should emit strict concrete-width VHDL and exact retirement outputs")
step("Compile concrete RV32 ADD and RV64 SUB retirement-projection products")
val rv32 = compile_strict_riscv_scalar_alu_retire_projection_product(
    "scalar_add_rv32", CoreConfig.rv32(), 0x002082B3)
val rv64 = compile_strict_riscv_scalar_alu_retire_projection_product(
    "scalar_sub_rv64", CoreConfig.rv64(), 0x402082B3)
expect(rv32.is_success()).to_equal(true)
expect(rv64.is_success()).to_equal(true)
expect(rv32.route).to_equal("hwir-gen2-scalar-alu-retire-projection-v1")
expect(rv64.route).to_equal("hwir-gen2-scalar-alu-retire-projection-v1")
expect(rv32.vhdl).to_contain("rs1_value : in std_logic_vector(31 downto 0)")
expect(rv64.vhdl).to_contain("rs1_value : in std_logic_vector(63 downto 0)")
expect(rv32.vhdl).to_contain("alu_result <= std_logic_vector(unsigned(rs1_value) + unsigned(rs2_value));")
expect(rv64.vhdl).to_contain("alu_result <= std_logic_vector(unsigned(rs1_value) - unsigned(rs2_value));")
expect(rv32.vhdl).to_contain("retire_rd_value <= alu_result when in_valid = '1' else zero_xlen;")
expect(rv32.vhdl).to_contain("retire_trap <= zero1;")
expect(rv64.vhdl).to_contain("retire_memory_write_mask <= zero32;")
expect(rv32.vhdl.contains("xlen =") or rv32.vhdl.contains("if xlen")).to_equal(false)
expect(rv64.vhdl.contains("xlen =") or rv64.vhdl.contains("if xlen")).to_equal(false)
```

</details>

#### should reject instructions outside the bounded ALU slice

- should reject instructions outside the bounded ALU slice
- Submit a load instruction to the bounded scalar ALU projection
   - Expected: load.is_err() is true
   - Expected: load.err().unwrap() equals `HWIR-E-RISCV-SCALAR-EMIT-SCOPE: scalar ALU slice admits only precise base-I A... (full value in folded executable source)`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("should reject instructions outside the bounded ALU slice")
step("Submit a load instruction to the bounded scalar ALU projection")
val load = strict_riscv_scalar_alu_retire_projection_hwir(
    "scalar_load_rejected", CoreConfig.rv32(), 0x00002083)
expect(load.is_err()).to_equal(true)
expect(load.err().unwrap()).to_equal("HWIR-E-RISCV-SCALAR-EMIT-SCOPE: scalar ALU slice admits only precise base-I ADD/SUB/AND/OR/XOR register or immediate rows")
```

</details>

#### should normalize invalid and x0 projection payloads and hash the exact structure

- should normalize invalid and x0 projection payloads and hash the exact structure
- Build repeated and cross-width ADD projections and inspect their normalized structure
   - Expected: first.is_ok() is true
   - Expected: repeated.is_ok() is true
   - Expected: rv64.is_ok() is true
   - Expected: module.structural_sha256() equals `repeated.ok().unwrap().structural_sha256()`
   - Expected: module.structural_sha256() == rv64.ok().unwrap().structural_sha256() is false
   - Expected: normalized_payloads equals `10`
   - Expected: rd_write_zero is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 27 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("should normalize invalid and x0 projection payloads and hash the exact structure")
step("Build repeated and cross-width ADD projections and inspect their normalized structure")
val first = strict_riscv_scalar_alu_retire_projection_hwir(
    "scalar_projection_hash", CoreConfig.rv32(), 0x00208033)
val repeated = strict_riscv_scalar_alu_retire_projection_hwir(
    "scalar_projection_hash", CoreConfig.rv32(), 0x00208033)
val rv64 = strict_riscv_scalar_alu_retire_projection_hwir(
    "scalar_projection_hash", CoreConfig.rv64(), 0x00208033)
expect(first.is_ok()).to_equal(true)
expect(repeated.is_ok()).to_equal(true)
expect(rv64.is_ok()).to_equal(true)
if first.is_ok() and repeated.is_ok() and rv64.is_ok():
    val module = first.ok().unwrap()
    expect(module.structural_sha256()).to_equal(repeated.ok().unwrap().structural_sha256())
    expect(module.structural_sha256() == rv64.ok().unwrap().structural_sha256()).to_equal(false)
    var normalized_payloads = 0
    for select in module.select_ops:
        if select.condition == "in_valid" and select.when_false.starts_with("zero"):
            normalized_payloads = normalized_payloads + 1
        if select.result == "retire_rd": expect(select.when_true).to_equal("zero5")
        if select.result == "retire_rd_value": expect(select.when_true).to_equal("zero_xlen")
    expect(normalized_payloads).to_equal(10)
    var rd_write_zero = false
    for op in module.comb_ops:
        if op.result == "retire_rd_write" and op.lhs == "zero1": rd_write_zero = true
    expect(rd_write_zero).to_equal(true)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler/50.mir/hwir_riscv_scalar_execution_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering shared emitted Gen2 scalar ALU retirement slice.
- shared emitted Gen2 scalar ALU retirement slice

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 4 |
| Active scenarios | 4 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-COMPILER`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `53407e8ce89d9895c27a0bb575d9211e77b8cddb53568a2047d8888ee260a133`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `53407e8ce89d9895c27a0bb575d9211e77b8cddb53568a2047d8888ee260a133`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `53407e8ce89d9895c27a0bb575d9211e77b8cddb53568a2047d8888ee260a133`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **87/100**; effective score: **87/100**; blockers: **0**.

SSpec documentization score: 87/100
source: test/01_unit/compiler/50.mir/hwir_riscv_scalar_execution_spec.spl
mirror: doc/06_spec/01_unit/compiler/50.mir/hwir_riscv_scalar_execution_spec.md (current)
findings: 10 blockers: 0
  narrative=100 structure=80 oracle=90
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/compiler/50.mir/hwir_riscv_scalar_execution_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/compiler/50.mir/hwir_riscv_scalar_execution_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, assumptions/preconditions, primary workflow, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/compiler/50.mir/hwir_riscv_scalar_execution_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-10): 1 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/compiler/50.mir/hwir_riscv_scalar_execution_spec.spl:44:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should monomorphize the same base-I ALU rows for RV32 and RV64' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/01_unit/compiler/50.mir/hwir_riscv_scalar_execution_spec.spl:44:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should monomorphize the same base-I ALU rows for RV32 and RV64' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/50.mir/hwir_riscv_scalar_execution_spec.spl:58:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should emit strict concrete-width VHDL and exact retirement outputs' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/01_unit/compiler/50.mir/hwir_riscv_scalar_execution_spec.spl:58:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should emit strict concrete-width VHDL and exact retirement outputs' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/50.mir/hwir_riscv_scalar_execution_spec.spl:81:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should reject instructions outside the bounded ALU slice' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/01_unit/compiler/50.mir/hwir_riscv_scalar_execution_spec.spl:81:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should reject instructions outside the bounded ALU slice' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/50.mir/hwir_riscv_scalar_execution_spec.spl:91:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should normalize invalid and x0 projection payloads and hash the exact structure' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
<!-- sspec-maintain:scorecard:end -->
