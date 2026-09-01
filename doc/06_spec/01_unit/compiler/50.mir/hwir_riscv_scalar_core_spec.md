# Hwir Riscv Scalar Core Specification

> Tests covering RISC-V Gen2 unified scalar elaboration.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 5 | 5 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Hwir Riscv Scalar Core Specification

## Scenarios

### RISC-V Gen2 unified scalar elaboration

#### should freeze separate RV32 and RV64 scalar products from one descriptor

- should freeze separate RV32 and RV64 scalar products from one descriptor
- Elaborate the same scalar descriptor for concrete RV32 and RV64 configurations
   - Expected: rv32.is_ok() is true
   - Expected: rv64.is_ok() is true
   - Expected: rv32.ok().unwrap().diagnostic() equals ``
   - Expected: rv64.ok().unwrap().diagnostic() equals ``
   - Expected: rv32.ok().unwrap().decoder.xlen equals `32`
   - Expected: rv64.ok().unwrap().decoder.xlen equals `64`
   - Expected: rv32.ok().unwrap().node_id.value == rv64.ok().unwrap().node_id.value is false
   - Expected: false is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("should freeze separate RV32 and RV64 scalar products from one descriptor")
step("Elaborate the same scalar descriptor for concrete RV32 and RV64 configurations")
val rv32 = riscv_gen2_scalar_elaboration(CoreConfig.rv32_zca_mission_critical(), "none")
val rv64 = riscv_gen2_scalar_elaboration(CoreConfig.rv64_zca_mission_critical(), "none")
expect(rv32.is_ok()).to_equal(true)
expect(rv64.is_ok()).to_equal(true)
if rv32.is_ok() and rv64.is_ok():
    expect(rv32.ok().unwrap().diagnostic()).to_equal("")
    expect(rv64.ok().unwrap().diagnostic()).to_equal("")
    expect(rv32.ok().unwrap().decoder.xlen).to_equal(32)
    expect(rv64.ok().unwrap().decoder.xlen).to_equal(64)
    expect(rv32.ok().unwrap().node_id.value == rv64.ok().unwrap().node_id.value).to_equal(false)
else:
    expect(false).to_equal(true)
```

</details>

#### should reject a provider that does not belong to the selected scalar ISA profile

- should reject a provider that does not belong to the selected scalar ISA profile
- Select a multiply/divide provider for a profile that excludes its capability
   - Expected: result.is_err() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("should reject a provider that does not belong to the selected scalar ISA profile")
step("Select a multiply/divide provider for a profile that excludes its capability")
val result = riscv_gen2_scalar_elaboration(CoreConfig.rv64_zca_mission_critical(), "dsp")
expect(result.is_err()).to_equal(true)
expect(result.err().unwrap()).to_equal(
    "RISCV-PROVIDER-E-MULDIV: an ISA profile without M or Zmmul must select no multiply/divide provider")
```

</details>

#### should not alias valid concrete scalar products that share a profile label

- should not alias valid concrete scalar products that share a profile label
- Elaborate two RV32 configurations that differ in physical-address width
   - Expected: standard_result.is_ok() is true
   - Expected: wider_pa_result.is_ok() is true
   - Expected: false is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 17 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("should not alias valid concrete scalar products that share a profile label")
step("Elaborate two RV32 configurations that differ in physical-address width")
val standard = CoreConfig.rv32_zca_mission_critical()
val wider_pa = CoreConfig(xlen: 32, physical_address_bits: 40,
    register_count: 32, profile: standard.profile,
    isa_profile: standard.isa_profile,
    compressed_decode_profile: standard.compressed_decode_profile)
val standard_result = riscv_gen2_scalar_elaboration(standard, "none")
val wider_pa_result = riscv_gen2_scalar_elaboration(wider_pa, "none")
expect(standard_result.is_ok()).to_equal(true)
expect(wider_pa_result.is_ok()).to_equal(true)
if standard_result.is_ok() and wider_pa_result.is_ok():
    expect(standard_result.ok().unwrap().node_id.value ==
        wider_pa_result.ok().unwrap().node_id.value).to_equal(false)
else:
    expect(false).to_equal(true)
```

</details>

#### should resolve an instruction only through the selected concrete scalar table

- should resolve an instruction only through the selected concrete scalar table
- Dispatch supported and RV64-only instruction words through the selected RV32 table
   - Expected: add.is_ok() is true
   - Expected: add.ok().unwrap().entry.id equals `rv.i.add`
   - Expected: add.ok().unwrap().provider equals `scalar-integer`
   - Expected: add.ok().unwrap().diagnostic() equals ``
   - Expected: false is true
   - Expected: rv64_word.is_err() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("should resolve an instruction only through the selected concrete scalar table")
step("Dispatch supported and RV64-only instruction words through the selected RV32 table")
val rv32 = riscv_gen2_scalar_elaboration(CoreConfig.rv32_zca_mission_critical(), "none").unwrap()
val add = riscv_gen2_scalar_dispatch(rv32, 0x00B50533)
val rv64_word = riscv_gen2_scalar_dispatch(rv32, 0x00B5053B)
expect(add.is_ok()).to_equal(true)
if add.is_ok():
    expect(add.ok().unwrap().entry.id).to_equal("rv.i.add")
    expect(add.ok().unwrap().provider).to_equal("scalar-integer")
    expect(add.ok().unwrap().diagnostic()).to_equal("")
else:
    expect(false).to_equal(true)
expect(rv64_word.is_err()).to_equal(true)
expect(rv64_word.err().unwrap()).to_equal(
    "RISCV-DECODER-E-ILLEGAL: instruction is not declared by the scalar decoder plan")
```

</details>

#### should fix an M instruction to the provider selected at elaboration

- should fix an M instruction to the provider selected at elaboration
- Elaborate an RV32IM product and dispatch its multiply instruction
   - Expected: multiply.is_ok() is true
   - Expected: multiply.ok().unwrap().entry.id equals `rv.m.mul`
   - Expected: multiply.ok().unwrap().provider equals `iterative`
   - Expected: false is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("should fix an M instruction to the provider selected at elaboration")
step("Elaborate an RV32IM product and dispatch its multiply instruction")
val config = CoreConfig(xlen: 32, physical_address_bits: 32,
    register_count: 32, profile: "riscv-gen2-rv32-im-critical",
    isa_profile: "rv32im", compressed_decode_profile: "none")
val scalar = riscv_gen2_scalar_elaboration(config, "iterative").unwrap()
val multiply = riscv_gen2_scalar_dispatch(scalar, 0x02000033)
expect(multiply.is_ok()).to_equal(true)
if multiply.is_ok():
    expect(multiply.ok().unwrap().entry.id).to_equal("rv.m.mul")
    expect(multiply.ok().unwrap().provider).to_equal("iterative")
else:
    expect(false).to_equal(true)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler/50.mir/hwir_riscv_scalar_core_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering RISC-V Gen2 unified scalar elaboration.
- RISC-V Gen2 unified scalar elaboration

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 5 |
| Active scenarios | 5 |
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

- Canonical SPipe generation for source `cf37dc686f69215544af7955cf6477f0cf90b659efc3ac8b649eecc481954d16`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `cf37dc686f69215544af7955cf6477f0cf90b659efc3ac8b649eecc481954d16`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `cf37dc686f69215544af7955cf6477f0cf90b659efc3ac8b649eecc481954d16`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **84/100**; effective score: **84/100**; blockers: **0**.

SSpec documentization score: 84/100
source: test/01_unit/compiler/50.mir/hwir_riscv_scalar_core_spec.spl
mirror: doc/06_spec/01_unit/compiler/50.mir/hwir_riscv_scalar_core_spec.md (current)
findings: 11 blockers: 0
  narrative=100 structure=75 oracle=80
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/compiler/50.mir/hwir_riscv_scalar_core_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/compiler/50.mir/hwir_riscv_scalar_core_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/compiler/50.mir/hwir_riscv_scalar_core_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-20): 2 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/compiler/50.mir/hwir_riscv_scalar_core_spec.spl:20:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should freeze separate RV32 and RV64 scalar products from one descriptor' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/01_unit/compiler/50.mir/hwir_riscv_scalar_core_spec.spl:20:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should freeze separate RV32 and RV64 scalar products from one descriptor' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/50.mir/hwir_riscv_scalar_core_spec.spl:38:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should reject a provider that does not belong to the selected scalar ISA profile' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/01_unit/compiler/50.mir/hwir_riscv_scalar_core_spec.spl:38:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should reject a provider that does not belong to the selected scalar ISA profile' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/50.mir/hwir_riscv_scalar_core_spec.spl:48:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should not alias valid concrete scalar products that share a profile label' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/01_unit/compiler/50.mir/hwir_riscv_scalar_core_spec.spl:48:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should not alias valid concrete scalar products that share a profile label' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/50.mir/hwir_riscv_scalar_core_spec.spl:68:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should resolve an instruction only through the selected concrete scalar table' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/01_unit/compiler/50.mir/hwir_riscv_scalar_core_spec.spl:87:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should fix an M instruction to the provider selected at elaboration' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
<!-- sspec-maintain:scorecard:end -->
