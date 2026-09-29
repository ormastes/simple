# Hwir Riscv Scalar Control Projection Specification

> Tests covering shared scalar branch and jump projection.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 7 | 7 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Hwir Riscv Scalar Control Projection Specification

## Scenarios

### shared scalar branch and jump projection

#### evaluates branch conditions and wrapped targets for both concrete XLENs

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- evaluates branch conditions and wrapped targets for both concrete XLENs


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("evaluates branch conditions and wrapped targets for both concrete XLENs")
for config in [CoreConfig.rv32(), CoreConfig.rv64()]:
    expect(control_value(config, 0x00208463, 0x1000, 1, 9, 2, 9,
        "redirect_target")).to_equal(0x1008)
    expect(control_value(config, 0x00208463, 0x1000, 1, 9, 2, 8,
        "redirect_valid")).to_equal(0)
    expect(control_value(config, 0x0020C463, 0x1000, 1, -1, 2, 1,
        "redirect_valid")).to_equal(1)
    expect(control_value(config, 0x0020F463, 0x1000, 1, -1, 2, 1,
        "redirect_valid")).to_equal(1)
```

</details>

#### clears JALR bit zero and rejects mismatched register binding

- clears JALR bit zero and rejects mismatched register binding


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("clears JALR bit zero and rejects mismatched register binding")
for config in [CoreConfig.rv32(), CoreConfig.rv64()]:
    expect(control_value(config, 0xFFF082E7, 0x2000, 1, 0x1000, 0, 0,
        "redirect_target")).to_equal(0x0FFE)
    expect(control_value(config, 0xFFF082E7, 0x2000, 3, 0x1000, 0, 0,
        "retire_valid")).to_equal(0)
    expect(control_value(config, 0xFFF082E7, 0x2000, 3, 0x1000, 0, 0,
        "retire_original_instruction")).to_equal(0)
```

</details>

#### projects IALIGN32 exceptions and admits IALIGN16 halfword targets

- projects IALIGN32 exceptions and admits IALIGN16 halfword targets


<details>
<summary>Executable SSpec</summary>

Runnable source: 23 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("projects IALIGN32 exceptions and admits IALIGN16 halfword targets")
# JAL x5,+2. Base-I has IALIGN=32, so target PC+2 traps; the admitted
# compressed product has IALIGN=16 and redirects to that same target.
val jal_plus_two: u32 = 0x002002EF
for config in [CoreConfig.rv32(), CoreConfig.rv64()]:
    expect(control_value(config, jal_plus_two, 0x1000, 0, 0, 0, 0,
        "execute_exception")).to_equal(1)
    expect(control_value(config, jal_plus_two, 0x1000, 0, 0, 0, 0,
        "retire_trap")).to_equal(1)
    expect(control_value(config, jal_plus_two, 0x1000, 0, 0, 0, 0,
        "retire_tval")).to_equal(0x1002)
    expect(control_value(config, jal_plus_two, 0x1000, 0, 0, 0, 0,
        "redirect_valid")).to_equal(0)
    expect(control_value(config, jal_plus_two, 0x1000, 0, 0, 0, 0,
        "retire_rd_write")).to_equal(0)
for config in [CoreConfig.rv32_zca(), CoreConfig.rv64_zca()]:
    expect(control_value(config, jal_plus_two, 0x1000, 0, 0, 0, 0,
        "execute_exception")).to_equal(0)
    expect(control_value(config, jal_plus_two, 0x1000, 0, 0, 0, 0,
        "redirect_target")).to_equal(0x1002)
    expect(control_value(config, jal_plus_two, 0x1000, 0, 0, 0, 0,
        "retire_rd_write")).to_equal(1)
```

</details>

#### checks taken B and post-bit-clear JALR targets against product IALIGN

- checks taken B and post-bit-clear JALR targets against product IALIGN


<details>
<summary>Executable SSpec</summary>

Runnable source: 17 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("checks taken B and post-bit-clear JALR targets against product IALIGN")
# BEQ +2 is misaligned only for IALIGN32. A non-taken branch never
# raises the target exception even though its encoded target is +2.
val beq_plus_two: u32 = 0x00208163
expect(control_value(CoreConfig.rv32(), beq_plus_two, 0x2000, 1, 7, 2, 7,
    "execute_exception")).to_equal(1)
expect(control_value(CoreConfig.rv32(), beq_plus_two, 0x2000, 1, 7, 2, 8,
    "execute_exception")).to_equal(0)
expect(control_value(CoreConfig.rv32_zca(), beq_plus_two, 0x2000, 1, 7, 2, 7,
    "redirect_target")).to_equal(0x2002)
# JALR clears bit zero first: 0x1003 becomes 0x1002 and still traps for
# IALIGN32, while the compressed product admits it.
expect(control_value(CoreConfig.rv64(), 0x000082E7, 0x3000, 1, 0x1003, 0, 0,
    "retire_tval")).to_equal(0x1002)
expect(control_value(CoreConfig.rv64_zca(), 0x000082E7, 0x3000, 1, 0x1003, 0, 0,
    "redirect_target")).to_equal(0x1002)
```

</details>

#### wraps boundary immediates and RV64 signed extremes

- wraps boundary immediates and RV64 signed extremes


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("wraps boundary immediates and RV64 signed extremes")
# JAL's most-negative immediate (-1048576) wraps at XLEN.
val jal_min: u32 = 0x800002EF
expect(control_value(CoreConfig.rv32(), jal_min, 0, 0, 0, 0, 0,
    "redirect_target")).to_equal(0xFFF00000)
expect(control_value(CoreConfig.rv64(), jal_min, 0, 0, 0, 0, 0,
    "redirect_target")).to_equal(-1048576)
# Signed BLT recognizes INT64_MIN < INT64_MAX; unsigned BLTU does not.
expect(control_value(CoreConfig.rv64(), 0x0020C463, 0x1000, 1,
    -9223372036854775807 - 1, 2, 9223372036854775807, "redirect_valid")).to_equal(1)
expect(control_value(CoreConfig.rv64(), 0x0020E463, 0x1000, 1,
    -9223372036854775807 - 1, 2, 9223372036854775807, "redirect_valid")).to_equal(0)
```

</details>

#### emits one typed VHDL projection for every admitted control row

- emits one typed VHDL projection for every admitted control row
   - Expected: rv32.is_success() is true
   - Expected: rv64.is_success() is true
   - Expected: rv32.route equals `hwir-gen2-scalar-control-projection-v1`
   - Expected: rv32.vhdl does not contain `"if xlen") or rv64.vhdl`


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("emits one typed VHDL projection for every admitted control row")
val instructions: [u32] = [0x00208463, 0x00209463, 0x0020C463, 0x0020D463,
    0x0020E463, 0x0020F463, 0x008002EF, 0xFFF082E7]
for instruction in instructions:
    val rv32 = compile_strict_riscv_scalar_control_projection_product(
        "control_rv32_" + instruction.to_text(), CoreConfig.rv32(), instruction)
    val rv64 = compile_strict_riscv_scalar_control_projection_product(
        "control_rv64_" + instruction.to_text(), CoreConfig.rv64(), instruction)
    expect(rv32.is_success()).to_equal(true)
    expect(rv64.is_success()).to_equal(true)
    expect(rv32.route).to_equal("hwir-gen2-scalar-control-projection-v1")
    expect(rv32.vhdl).to_contain("redirect_target : out std_logic_vector(31 downto 0)")
    expect(rv64.vhdl).to_contain("redirect_target : out std_logic_vector(63 downto 0)")
    expect(rv32.vhdl.contains("if xlen") or rv64.vhdl.contains("if xlen")).to_equal(false)
```

</details>

#### retains deterministic graph identity and normalized invalid payloads

- retains deterministic graph identity and normalized invalid payloads
   - Expected: first.is_ok() is true
   - Expected: repeated.is_ok() is true
   - Expected: rv64.is_ok() is true
   - Expected: normalized equals `11`


<details>
<summary>Executable SSpec</summary>

Runnable source: 21 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("retains deterministic graph identity and normalized invalid payloads")
val first = strict_riscv_scalar_control_projection_hwir(
    "control_hash", CoreConfig.rv32(), 0xFFF082E7)
val repeated = strict_riscv_scalar_control_projection_hwir(
    "control_hash", CoreConfig.rv32(), 0xFFF082E7)
val rv64 = strict_riscv_scalar_control_projection_hwir(
    "control_hash", CoreConfig.rv64(), 0xFFF082E7)
expect(first.is_ok()).to_equal(true)
expect(repeated.is_ok()).to_equal(true)
expect(rv64.is_ok()).to_equal(true)
if first.is_ok() and repeated.is_ok() and rv64.is_ok():
    expect(first.ok().unwrap().structural_sha256()).to_equal(
        repeated.ok().unwrap().structural_sha256())
    expect(first.ok().unwrap().structural_sha256() ==
        rv64.ok().unwrap().structural_sha256()).to_equal(false)
    var normalized = 0
    for select in first.ok().unwrap().select_ops:
        if select.result.starts_with("retire_") and select.when_false.starts_with("zero"):
            normalized = normalized + 1
    expect(normalized).to_equal(11)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler/50.mir/hwir_riscv_scalar_control_projection_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering shared scalar branch and jump projection.
- shared scalar branch and jump projection

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 7 |
| Active scenarios | 7 |
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

- Canonical SPipe generation for source `7ac7b43a04effece6cad23dbb77c917155de7f92487d2078730e73357eda9ab3`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `7ac7b43a04effece6cad23dbb77c917155de7f92487d2078730e73357eda9ab3`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `7ac7b43a04effece6cad23dbb77c917155de7f92487d2078730e73357eda9ab3`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **90/100**; effective score: **90/100**; blockers: **0**.

SSpec documentization score: 90/100
source: test/01_unit/compiler/50.mir/hwir_riscv_scalar_control_projection_spec.spl
mirror: doc/06_spec/01_unit/compiler/50.mir/hwir_riscv_scalar_control_projection_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=90
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/compiler/50.mir/hwir_riscv_scalar_control_projection_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/compiler/50.mir/hwir_riscv_scalar_control_projection_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/compiler/50.mir/hwir_riscv_scalar_control_projection_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-10): 1 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/compiler/50.mir/hwir_riscv_scalar_control_projection_spec.spl:36:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'evaluates branch conditions and wrapped targets for both concrete XLENs' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/50.mir/hwir_riscv_scalar_control_projection_spec.spl:49:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'clears JALR bit zero and rejects mismatched register binding' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/50.mir/hwir_riscv_scalar_control_projection_spec.spl:60:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'projects IALIGN32 exceptions and admits IALIGN16 halfword targets' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
