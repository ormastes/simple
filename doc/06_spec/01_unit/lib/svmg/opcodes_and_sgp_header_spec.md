# Opcodes And Sgp Header Specification

> Tests covering svmg opcode table round trip (Task D1), svmg SGP header round trip (Task D1).

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 6 | 6 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Opcodes And Sgp Header Specification

## Scenarios

### svmg opcode table round trip (Task D1)

#### has exactly the 50 mnemonics in design doc §4.3's opcode set

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- has exactly the 50 mnemonics in design doc §4.3's opcode set


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("has exactly the 50 mnemonics in design doc §4.3's opcode set")
# Guards against a silently-dropped entry shrinking "every opcode"
# coverage below to "every opcode this list still remembers".
# Count: NOP/HALT/TRAP(3) + PUSHI/PUSHF/DUP/DROP/SWAP(5) +
# ADD/SUB/MUL/DIV/REM(5) + FADD/FSUB/FMUL/FDIV(4) +
# AND/OR/XOR/SHL/SHR/SAR(6) + EQ/NE/LT/LE/GT/GE(6) +
# FEQ/FNE/FLT/FLE/FGT/FGE(6) + LOAD32/STORE32/LOAD8/STORE8(4) +
# JMP/JZ/JNZ(3) + CALL/RET(2) + SYS_PUTC/SYS_EXIT/SYS_RESULT(3) +
# TID/NTID/PARFOR(3) = 50.
assert_equal(all_mnemonics().len(), 50)
```

</details>

#### assembles and disassembles every mnemonic in the opcode set

- assembles and disassembles every mnemonic in the opcode set


<details>
<summary>Executable SSpec</summary>

Runnable source: 23 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("assembles and disassembles every mnemonic in the opcode set")
for mnemonic in all_mnemonics():
    val opcode = mnemonic_to_opcode(mnemonic)
    val kind = operand_kind_of(opcode)
    val line = _line_for(mnemonic)
    val bytes = svmg_asm(line)
    val decoded = disasm(bytes)
    val decoded_tokens = decoded.trim().split(" ")
    assert_equal(decoded_tokens[0], mnemonic)
    if kind != OPERAND_NONE:
        assert_equal(decoded_tokens.len(), 2)
        if kind == OPERAND_IMM32F:
            val original = _sample_operand(mnemonic).to_f64()
            val round_tripped = decoded_tokens[1].to_f64()
            val diff = original - round_tripped
            assert_true(diff > -0.001 and diff < 0.001)
        else:
            val original = try_parse_int(_sample_operand(mnemonic))
            val round_tripped = try_parse_int(decoded_tokens[1])
            assert_equal(round_tripped, original)
    else:
        assert_equal(decoded_tokens.len(), 1)
```

</details>

#### assembles a multi-instruction program in program order

- assembles a multi-instruction program in program order


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("assembles a multi-instruction program in program order")
val bytes = svmg_asm("PUSHI 1\nPUSHI 2\nADD\nHALT 0")
val decoded = disasm(bytes)
assert_equal(decoded, "PUSHI 1\nPUSHI 2\nADD\nHALT 0")
```

</details>

#### ignores comments and blank lines

- ignores comments and blank lines


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("ignores comments and blank lines")
val bytes = svmg_asm("# a comment\n\nNOP  # trailing comment\n\nRET")
val decoded = disasm(bytes)
assert_equal(decoded, "NOP\nRET")
```

</details>

### svmg SGP header round trip (Task D1)

#### round-trips every field through encode/decode

- round-trips every field through encode/decode


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("round-trips every field through encode/decode")
val header = sgp_header_new(36, 20, 56, 8, 50000000, 4)
val bytes = encode_sgp_header(header)
assert_equal(bytes.len(), SGP_HEADER_SIZE)
val decoded = decode_sgp_header(bytes)
assert_equal(decoded.magic, SGP_MAGIC)
assert_equal(decoded.version, SGP_VERSION)
assert_equal(decoded.code_off, 36)
assert_equal(decoded.code_len, 20)
assert_equal(decoded.data_off, 56)
assert_equal(decoded.data_len, 8)
assert_equal(decoded.step_budget, 50000000)
assert_equal(decoded.entry_pc, 4)
assert_equal(decoded.reserved0, 0)
```

</details>

#### round-trips large u32-range values (step_budget near u32 max)

- round-trips large u32-range values (step_budget near u32 max)


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("round-trips large u32-range values (step_budget near u32 max)")
val header = sgp_header_new(36, 65535, 65571, 65535, 4000000000, 65535)
val bytes = encode_sgp_header(header)
val decoded = decode_sgp_header(bytes)
assert_equal(decoded.step_budget, 4000000000)
assert_equal(decoded.code_len, 65535)
assert_equal(decoded.entry_pc, 65535)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/svmg/opcodes_and_sgp_header_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering svmg opcode table round trip (Task D1), svmg SGP header round trip (Task D1).
- svmg opcode table round trip (Task D1)
- svmg SGP header round trip (Task D1)

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 6 |
| Active scenarios | 6 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-UNIT`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `0615242b5991951d6afa6604ca1d52ae1caf1291b6b3c06e322574aebd3abd62`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `0615242b5991951d6afa6604ca1d52ae1caf1291b6b3c06e322574aebd3abd62`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `0615242b5991951d6afa6604ca1d52ae1caf1291b6b3c06e322574aebd3abd62`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/01_unit/lib/svmg/opcodes_and_sgp_header_spec.spl
mirror: doc/06_spec/01_unit/lib/svmg/opcodes_and_sgp_header_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/lib/svmg/opcodes_and_sgp_header_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/lib/svmg/opcodes_and_sgp_header_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/lib/svmg/opcodes_and_sgp_header_spec.spl:47:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'has exactly the 50 mnemonics in design doc §4.3's opcode set' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/svmg/opcodes_and_sgp_header_spec.spl:60:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'assembles and disassembles every mnemonic in the opcode set' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/svmg/opcodes_and_sgp_header_spec.spl:85:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'assembles a multi-instruction program in program order' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
