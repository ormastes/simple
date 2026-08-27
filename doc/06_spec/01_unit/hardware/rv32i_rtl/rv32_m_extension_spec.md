# Rv32 M Extension Specification

> Tests covering RV32M arithmetic owner.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 3 | 3 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Rv32 M Extension Specification

## Scenarios

### RV32M arithmetic owner

#### decodes only OP/funct7=1 and executes all multiply high words

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- decodes only OP/funct7=1 and executes all multiply high words
   - Expected: mul.operation equals `RV32M_MUL`
   - Expected: rv32m_execute(RV32M_MUL, 0xFFFF_FFFF, 2) equals `0xFFFF_FFFE`
   - Expected: rv32m_execute(RV32M_MULH, -1, -1) equals `0`
   - Expected: rv32m_execute(RV32M_MULHSU, -1, 2) equals `0xFFFF_FFFF`
   - Expected: rv32m_execute(RV32M_MULHU, 0xFFFF_FFFF, 2) equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-HARDWARE
step("decodes only OP/funct7=1 and executes all multiply high words")
val mul = rv32m_decode(0x02000033)
expect(mul.matched).to_be(true)
expect(mul.operation).to_equal(RV32M_MUL)
expect(rv32m_decode(0x00000033).matched).to_be(false)
expect(rv32m_execute(RV32M_MUL, 0xFFFF_FFFF, 2)).to_equal(0xFFFF_FFFE)
expect(rv32m_execute(RV32M_MULH, -1, -1)).to_equal(0)
expect(rv32m_execute(RV32M_MULHSU, -1, 2)).to_equal(0xFFFF_FFFF)
expect(rv32m_execute(RV32M_MULHU, 0xFFFF_FFFF, 2)).to_equal(1)
```

</details>

#### implements signed and unsigned divide/remainder corner cases

- implements signed and unsigned divide/remainder corner cases
   - Expected: rv32m_execute(RV32M_DIV, -20, 3) equals `0xFFFF_FFFA`
   - Expected: rv32m_execute(RV32M_REM, -20, 3) equals `0xFFFF_FFFE`
   - Expected: rv32m_execute(RV32M_DIV, 0x8000_0000, -1) equals `0x8000_0000`
   - Expected: rv32m_execute(RV32M_REM, 0x8000_0000, -1) equals `0`
   - Expected: rv32m_execute(RV32M_DIV, 7, 0) equals `0xFFFF_FFFF`
   - Expected: rv32m_execute(RV32M_REM, 0x8000_0005, 0) equals `0x8000_0005`
   - Expected: rv32m_execute(RV32M_DIVU, 0xFFFF_FFFF, 2) equals `0x7FFF_FFFF`
   - Expected: rv32m_execute(RV32M_DIVU, 7, 0) equals `0xFFFF_FFFF`
   - Expected: rv32m_execute(RV32M_REMU, 0xFFFF_FFFF, 2) equals `1`
   - Expected: rv32m_execute(RV32M_REMU, 0x8000_0005, 0) equals `0x8000_0005`


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-HARDWARE
step("implements signed and unsigned divide/remainder corner cases")
expect(rv32m_execute(RV32M_DIV, -20, 3)).to_equal(0xFFFF_FFFA)
expect(rv32m_execute(RV32M_REM, -20, 3)).to_equal(0xFFFF_FFFE)
expect(rv32m_execute(RV32M_DIV, 0x8000_0000, -1)).to_equal(0x8000_0000)
expect(rv32m_execute(RV32M_REM, 0x8000_0000, -1)).to_equal(0)
expect(rv32m_execute(RV32M_DIV, 7, 0)).to_equal(0xFFFF_FFFF)
expect(rv32m_execute(RV32M_REM, 0x8000_0005, 0)).to_equal(0x8000_0005)
expect(rv32m_execute(RV32M_DIVU, 0xFFFF_FFFF, 2)).to_equal(0x7FFF_FFFF)
expect(rv32m_execute(RV32M_DIVU, 7, 0)).to_equal(0xFFFF_FFFF)
expect(rv32m_execute(RV32M_REMU, 0xFFFF_FFFF, 2)).to_equal(1)
expect(rv32m_execute(RV32M_REMU, 0x8000_0005, 0)).to_equal(0x8000_0005)
```

</details>

#### uses a 32-step result-valid handshake with exact iterative corners

- uses a 32-step result-valid handshake with exact iterative corners
   - Expected: cycles equals `32`
   - Expected: state.result equals `1`
   - Expected: sequential_result(RV32M_MULH, -1, 2) equals `0xFFFF_FFFF`
   - Expected: sequential_result(RV32M_MULHSU, 0x8000_0000, 2) equals `0xFFFF_FFFF`
   - Expected: sequential_result(RV32M_MULHU, 0xFFFF_FFFF, 0xFFFF_FFFF) equals `0xFFFF_FFFE`
   - Expected: sequential_result(RV32M_DIV, 0x8000_0000, -1) equals `0x8000_0000`
   - Expected: sequential_result(RV32M_REM, 0x8000_0000, -1) equals `0`
   - Expected: sequential_result(RV32M_DIVU, 0xFFFF_FFFF, 2) equals `0x7FFF_FFFF`
   - Expected: sequential_result(RV32M_REMU, 0xFFFF_FFFF, 2) equals `1`
   - Expected: div_zero.result equals `0xFFFF_FFFF`


<details>
<summary>Executable SSpec</summary>

Runnable source: 27 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-HARDWARE
step("uses a 32-step result-valid handshake with exact iterative corners")
var state = rv32m_start(rv32m_create(), RV32M_MULHU, 0xFFFF_FFFF, 2)
expect(state.busy).to_be(true)
expect(state.result_valid).to_be(false)
var cycles = 0
while state.busy:
    state = rv32m_tick(state)
    cycles = cycles + 1
expect(cycles).to_equal(32)
expect(state.result_valid).to_be(true)
expect(state.result).to_equal(1)
expect(rv32m_tick(state).result_valid).to_be(true)
state = rv32m_start(state, RV32M_DIV, 7, 3)
expect(state.result_valid).to_be(false)

expect(sequential_result(RV32M_MULH, -1, 2)).to_equal(0xFFFF_FFFF)
expect(sequential_result(RV32M_MULHSU, 0x8000_0000, 2)).to_equal(0xFFFF_FFFF)
expect(sequential_result(RV32M_MULHU, 0xFFFF_FFFF, 0xFFFF_FFFF)).to_equal(0xFFFF_FFFE)
expect(sequential_result(RV32M_DIV, 0x8000_0000, -1)).to_equal(0x8000_0000)
expect(sequential_result(RV32M_REM, 0x8000_0000, -1)).to_equal(0)
expect(sequential_result(RV32M_DIVU, 0xFFFF_FFFF, 2)).to_equal(0x7FFF_FFFF)
expect(sequential_result(RV32M_REMU, 0xFFFF_FFFF, 2)).to_equal(1)
val div_zero = rv32m_tick(rv32m_start(rv32m_create(), RV32M_DIV, 7, 0))
expect(div_zero.busy).to_be(false)
expect(div_zero.result_valid).to_be(true)
expect(div_zero.result).to_equal(0xFFFF_FFFF)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Hardware & OS |
| Status | Active |
| Source | `test/01_unit/hardware/rv32i_rtl/rv32_m_extension_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering RV32M arithmetic owner.
- RV32M arithmetic owner

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 3 |
| Active scenarios | 3 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-HARDWARE`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `637d1605bce463e646333e556d99e088bf47bd8e8128a3561a0ce5f807e4cbb3`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `637d1605bce463e646333e556d99e088bf47bd8e8128a3561a0ce5f807e4cbb3`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `637d1605bce463e646333e556d99e088bf47bd8e8128a3561a0ce5f807e4cbb3`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **86/100**; effective score: **86/100**; blockers: **0**.

SSpec documentization score: 86/100
source: test/01_unit/hardware/rv32i_rtl/rv32_m_extension_spec.spl
mirror: doc/06_spec/01_unit/hardware/rv32i_rtl/rv32_m_extension_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/hardware/rv32i_rtl/rv32_m_extension_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/hardware/rv32i_rtl/rv32_m_extension_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/hardware/rv32i_rtl/rv32_m_extension_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 8 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/hardware/rv32i_rtl/rv32_m_extension_spec.spl:24:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'decodes only OP/funct7=1 and executes all multiply high words' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/hardware/rv32i_rtl/rv32_m_extension_spec.spl:36:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'implements signed and unsigned divide/remainder corner cases' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/hardware/rv32i_rtl/rv32_m_extension_spec.spl:50:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'uses a 32-step result-valid handshake with exact iterative corners' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
