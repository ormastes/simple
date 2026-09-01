# Ref Vm Specification

> Tests covering svmg reference VM (Task D2) — arithmetic and SYS_RESULT, svmg reference VM (Task D2) — control flow, svmg reference VM (Task D2) — traps, svmg reference VM (Task D2) — step budget, svmg reference VM (Task D2) — PUTC/RESULT/EXIT land in the correct arena offsets.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 19 | 19 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Ref Vm Specification

## Scenarios

### svmg reference VM (Task D2) — arithmetic and SYS_RESULT

#### adds two integers and records the result

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- adds two integers and records the result


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("adds two integers and records the result")
# PUSHI 1(pass) PUSHI 3 PUSHI 4 ADD SYS_RESULT HALT 0
val bytes = svmg_asm("PUSHI 1\nPUSHI 3\nPUSHI 4\nADD\nSYS_RESULT\nHALT 0")
val result = assemble_and_run(bytes, 1000, 0)
assert_equal(result.halted, true)
assert_equal(result.trapped, false)
assert_equal(result.timed_out, false)
assert_equal(result.record_count, 1)
val records = read_records(result.arena, result.log_cap, result.record_count)
assert_equal(records[0].passed, 1)
assert_equal(records[0].value, 7)
assert_equal(result.sentinel, SENTINEL_EXIT_MASK | 0)
```

</details>

#### computes SUB/MUL/DIV/REM correctly (10, 3)

- computes SUB/MUL/DIV/REM correctly (10, 3)


<details>
<summary>Executable SSpec</summary>

Runnable source: 21 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("computes SUB/MUL/DIV/REM correctly (10, 3)")
val bytes = svmg_asm("PUSHI 1\nPUSHI 10\nPUSHI 3\nSUB\nSYS_RESULT\nHALT 0")
val result = assemble_and_run(bytes, 1000, 0)
val records = read_records(result.arena, result.log_cap, result.record_count)
assert_equal(records[0].value, 7)

val bytes2 = svmg_asm("PUSHI 1\nPUSHI 10\nPUSHI 3\nMUL\nSYS_RESULT\nHALT 0")
val result2 = assemble_and_run(bytes2, 1000, 0)
val records2 = read_records(result2.arena, result2.log_cap, result2.record_count)
assert_equal(records2[0].value, 30)

val bytes3 = svmg_asm("PUSHI 1\nPUSHI 10\nPUSHI 3\nDIV\nSYS_RESULT\nHALT 0")
val result3 = assemble_and_run(bytes3, 1000, 0)
val records3 = read_records(result3.arena, result3.log_cap, result3.record_count)
assert_equal(records3[0].value, 3)

val bytes4 = svmg_asm("PUSHI 1\nPUSHI 10\nPUSHI 3\nREM\nSYS_RESULT\nHALT 0")
val result4 = assemble_and_run(bytes4, 1000, 0)
val records4 = read_records(result4.arena, result4.log_cap, result4.record_count)
assert_equal(records4[0].value, 1)
```

</details>

#### computes bitwise AND/OR/XOR/SHL/SHR

- computes bitwise AND/OR/XOR/SHL/SHR


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("computes bitwise AND/OR/XOR/SHL/SHR")
val bytes = svmg_asm("PUSHI 1\nPUSHI 12\nPUSHI 10\nAND\nSYS_RESULT\nHALT 0")
val result = assemble_and_run(bytes, 1000, 0)
val records = read_records(result.arena, result.log_cap, result.record_count)
assert_equal(records[0].value, 8)

val bytes2 = svmg_asm("PUSHI 1\nPUSHI 1\nPUSHI 4\nSHL\nSYS_RESULT\nHALT 0")
val result2 = assemble_and_run(bytes2, 1000, 0)
val records2 = read_records(result2.arena, result2.log_cap, result2.record_count)
assert_equal(records2[0].value, 16)
```

</details>

#### SHR is logical (zero-fill) and SAR is arithmetic (sign-preserving) on negatives

- SHR is logical (zero-fill) and SAR is arithmetic (sign-preserving) on negatives


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("SHR is logical (zero-fill) and SAR is arithmetic (sign-preserving) on negatives")
# -1 (0xFFFFFFFF) SHR 28 must be 15 (0x0000000F): logical, no sign fill.
val bytes = svmg_asm("PUSHI 1\nPUSHI -1\nPUSHI 28\nSHR\nSYS_RESULT\nHALT 0")
val result = assemble_and_run(bytes, 1000, 0)
val records = read_records(result.arena, result.log_cap, result.record_count)
assert_equal(records[0].value, 15)

# -16 SAR 2 must be -4: arithmetic, sign preserved.
val bytes2 = svmg_asm("PUSHI 1\nPUSHI -16\nPUSHI 2\nSAR\nSYS_RESULT\nHALT 0")
val result2 = assemble_and_run(bytes2, 1000, 0)
val records2 = read_records(result2.arena, result2.log_cap, result2.record_count)
assert_equal(records2[0].value, -4)
```

</details>

#### computes float FADD via PUSHF

- computes float FADD via PUSHF


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("computes float FADD via PUSHF")
val bytes = svmg_asm("PUSHI 1\nPUSHF 1.5\nPUSHF 2.25\nFADD\nSYS_RESULT\nHALT 0")
val result = assemble_and_run(bytes, 1000, 0)
val records = read_records(result.arena, result.log_cap, result.record_count)
# FADD's result bit pattern for 3.75f (1.5 + 2.25): sign=0,
# exp=128(1+127), mantissa=0b111<<20 -> 0x40700000 = 1081081856.
assert_equal(records[0].value, 1081081856)
```

</details>

### svmg reference VM (Task D2) — control flow

#### JMP skips a dead HALT and reaches the live SYS_RESULT

- JMP skips a dead HALT and reaches the live SYS_RESULT


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("JMP skips a dead HALT and reaches the live SYS_RESULT")
# pc0 JMP 2 (len3,next3, target = next(3)+2 = 5)
# pc3 HALT 99 (len2)             <- skipped
# pc5 PUSHI 1 (len5,next10)
# pc10 PUSHI 55 (len5,next15)
# pc15 SYS_RESULT (len1,next16)
# pc16 HALT 0 (len2)
val bytes = svmg_asm("JMP 2\nHALT 99\nPUSHI 1\nPUSHI 55\nSYS_RESULT\nHALT 0")
val result = assemble_and_run(bytes, 1000, 0)
assert_equal(result.record_count, 1)
val records = read_records(result.arena, result.log_cap, result.record_count)
assert_equal(records[0].value, 55)
assert_equal(result.sentinel, SENTINEL_EXIT_MASK | 0)
```

</details>

#### JZ takes the zero branch

- JZ takes the zero branch


<details>
<summary>Executable SSpec</summary>

Runnable source: 18 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("JZ takes the zero branch")
# pc0 PUSHI 0 (len5,next5)                 cond = 0
# pc5 JZ 13 (len3,next8, target=8+13=21)
# pc8 PUSHI 1 (len5,next13)                 nonzero-path pass
# pc13 PUSHI 111 (len5,next18)               nonzero-path value
# pc18 SYS_RESULT (len1,next19)
# pc19 HALT 1 (len2,next21)
# pc21 PUSHI 1 (len5)                        zero-path pass  <- JZ lands here
# pc26 PUSHI 222 (len5)
# pc31 SYS_RESULT (len1)
# pc32 HALT 0 (len2)
val bytes = svmg_asm("PUSHI 0\nJZ 13\nPUSHI 1\nPUSHI 111\nSYS_RESULT\nHALT 1\nPUSHI 1\nPUSHI 222\nSYS_RESULT\nHALT 0")
val result = assemble_and_run(bytes, 1000, 0)
assert_equal(result.record_count, 1)
val records = read_records(result.arena, result.log_cap, result.record_count)
assert_equal(records[0].value, 222)
assert_equal(result.sentinel, SENTINEL_EXIT_MASK | 0)
```

</details>

#### JNZ takes the nonzero branch

- JNZ takes the nonzero branch


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("JNZ takes the nonzero branch")
# Same shape as the JZ program but with a nonzero condition and JNZ.
val bytes = svmg_asm("PUSHI 5\nJNZ 13\nPUSHI 1\nPUSHI 111\nSYS_RESULT\nHALT 1\nPUSHI 1\nPUSHI 222\nSYS_RESULT\nHALT 0")
val result = assemble_and_run(bytes, 1000, 0)
val records = read_records(result.arena, result.log_cap, result.record_count)
assert_equal(records[0].value, 222)
```

</details>

#### CALL/RET runs a subroutine and returns to the caller

- CALL/RET runs a subroutine and returns to the caller


<details>
<summary>Executable SSpec</summary>

Runnable source: 18 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("CALL/RET runs a subroutine and returns to the caller")
# pc0 PUSHI 21 (len5,next5)
# pc5 CALL 17 (len3,next8)          -> pushes return addr 8, jumps to 17
# pc8 PUSHI 1 (len5,next13)          <- RET lands back here
# pc13 SWAP (len1,next14)
# pc14 SYS_RESULT (len1,next15)
# pc15 HALT 0 (len2,next17)
# pc17 DUP (len1,next18)             <- subroutine "double"
# pc18 ADD (len1,next19)
# pc19 RET (len1)
val bytes = svmg_asm("PUSHI 21\nCALL 17\nPUSHI 1\nSWAP\nSYS_RESULT\nHALT 0\nDUP\nADD\nRET")
val result = assemble_and_run(bytes, 1000, 0)
assert_equal(result.record_count, 1)
val records = read_records(result.arena, result.log_cap, result.record_count)
assert_equal(records[0].passed, 1)
assert_equal(records[0].value, 42)
assert_equal(result.sentinel, SENTINEL_EXIT_MASK | 0)
```

</details>

### svmg reference VM (Task D2) — traps

#### traps LOAD32 out-of-bounds with CMD_RESULT(pass=0, value=TRAP_OOB) + CMD_EXIT(0x7F)

- traps LOAD32 out-of-bounds with CMD_RESULT(pass=0, value=TRAP_OOB) + CMD_EXIT(0x7F)


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("traps LOAD32 out-of-bounds with CMD_RESULT(pass=0, value=TRAP_OOB) + CMD_EXIT(0x7F)")
val bytes = svmg_asm("PUSHI 65536\nLOAD32\nHALT 0")
val result = assemble_and_run(bytes, 1000, 0)
assert_equal(result.trapped, true)
assert_equal(result.halted, true)
assert_equal(result.record_count, 1)
val records = read_records(result.arena, result.log_cap, result.record_count)
assert_equal(records[0].passed, 0)
assert_equal(records[0].value, TRAP_OOB)
assert_equal(result.sentinel, SENTINEL_EXIT_MASK | TRAP_OOB_EXIT_CODE)
```

</details>

#### traps STORE8 out-of-bounds (negative offset)

- traps STORE8 out-of-bounds (negative offset)


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("traps STORE8 out-of-bounds (negative offset)")
val bytes = svmg_asm("PUSHI -1\nPUSHI 7\nSTORE8\nHALT 0")
val result = assemble_and_run(bytes, 1000, 0)
assert_equal(result.trapped, true)
val records = read_records(result.arena, result.log_cap, result.record_count)
assert_equal(records[0].value, TRAP_OOB)
```

</details>

#### does NOT trap a LOAD32 at the last valid word

- does NOT trap a LOAD32 at the last valid word


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("does NOT trap a LOAD32 at the last valid word")
val bytes = svmg_asm("PUSHI 65532\nLOAD32\nDROP\nHALT 0")
val result = assemble_and_run(bytes, 1000, 0)
assert_equal(result.trapped, false)
assert_equal(result.sentinel, SENTINEL_EXIT_MASK | 0)
```

</details>

#### traps DIV by zero

- traps DIV by zero


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("traps DIV by zero")
val bytes = svmg_asm("PUSHI 5\nPUSHI 0\nDIV\nHALT 0")
val result = assemble_and_run(bytes, 1000, 0)
assert_equal(result.trapped, true)
val records = read_records(result.arena, result.log_cap, result.record_count)
assert_equal(records[0].value, TRAP_DIV0)
```

</details>

#### explicit TRAP opcode writes its immediate code as the result value

- explicit TRAP opcode writes its immediate code as the result value


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("explicit TRAP opcode writes its immediate code as the result value")
val bytes = svmg_asm("TRAP 42\nHALT 0")
val result = assemble_and_run(bytes, 1000, 0)
assert_equal(result.trapped, true)
val records = read_records(result.arena, result.log_cap, result.record_count)
assert_equal(records[0].value, 42)
assert_equal(result.sentinel, SENTINEL_EXIT_MASK | TRAP_OOB_EXIT_CODE)
```

</details>

### svmg reference VM (Task D2) — step budget

<details>
<summary>Advanced: exhausts the step budget on an infinite loop and writes SENTINEL_TIMEOUT</summary>

#### exhausts the step budget on an infinite loop and writes SENTINEL_TIMEOUT

- exhausts the step budget on an infinite loop and writes SENTINEL_TIMEOUT


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("exhausts the step budget on an infinite loop and writes SENTINEL_TIMEOUT")
# pc0 NOP (len1,next1)
# pc1 JMP -4 (len3,next4, target = 4-4 = 0)
val bytes = svmg_asm("NOP\nJMP -4")
val result = assemble_and_run(bytes, 10, 0)
assert_equal(result.timed_out, true)
assert_equal(result.halted, true)
assert_equal(result.trapped, false)
assert_equal(result.sentinel, SENTINEL_TIMEOUT)
assert_equal(result.steps_used, 10)
```

</details>


</details>

#### does not time out when the program halts before the budget runs out

- does not time out when the program halts before the budget runs out


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("does not time out when the program halts before the budget runs out")
val bytes = svmg_asm("NOP\nHALT 0")
val result = assemble_and_run(bytes, 1000, 0)
assert_equal(result.timed_out, false)
assert_equal(result.sentinel, SENTINEL_EXIT_MASK | 0)
```

</details>

### svmg reference VM (Task D2) — PUTC/RESULT/EXIT land in the correct arena offsets

#### SYS_PUTC bytes land in the LOG ring and decode back to the expected text

- SYS_PUTC bytes land in the LOG ring and decode back to the expected text


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("SYS_PUTC bytes land in the LOG ring and decode back to the expected text")
val bytes = svmg_asm("PUSHI 72\nSYS_PUTC\nPUSHI 105\nSYS_PUTC\nHALT 0")
val result = assemble_and_run(bytes, 1000, 0)
assert_equal(read_log(result.arena, result.log_cap), "Hi")
```

</details>

#### the exit sentinel is written at the documented RAM_SENTINEL_OFFSET

- the exit sentinel is written at the documented RAM_SENTINEL_OFFSET


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("the exit sentinel is written at the documented RAM_SENTINEL_OFFSET")
val bytes = svmg_asm("HALT 5")
val result = assemble_and_run(bytes, 1000, 0)
# Read the sentinel directly out of the raw arena bytes at the
# design §3.1 offset, independent of the ref_vm's own helper, to
# prove the write landed at the documented address and not just
# wherever read_sentinel happens to look.
val raw = _u32_le(result.arena, RAM_SENTINEL_OFFSET)
assert_equal(raw, SENTINEL_EXIT_MASK | 5)
assert_true(RAM_SENTINEL_OFFSET < ARENA_DATA_SIZE)
```

</details>

#### SYS_EXIT pops its code and writes the exit sentinel

- SYS_EXIT pops its code and writes the exit sentinel


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("SYS_EXIT pops its code and writes the exit sentinel")
val bytes = svmg_asm("PUSHI 1\nPUSHI 9\nSYS_RESULT\nPUSHI 3\nSYS_EXIT")
val result = assemble_and_run(bytes, 1000, 0)
assert_equal(result.record_count, 1)
val records = read_records(result.arena, result.log_cap, result.record_count)
assert_equal(records[0].value, 9)
assert_equal(result.sentinel, SENTINEL_EXIT_MASK | 3)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/svmg/ref_vm_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering svmg reference VM (Task D2) — arithmetic and SYS_RESULT, svmg reference VM (Task D2) — control flow, svmg reference VM (Task D2) — traps, svmg reference VM (Task D2) — step budget, svmg reference VM (Task D2) — PUTC/RESULT/EXIT land in the correct arena offsets.
- svmg reference VM (Task D2) — arithmetic and SYS_RESULT
- svmg reference VM (Task D2) — control flow
- svmg reference VM (Task D2) — traps
- svmg reference VM (Task D2) — step budget
- svmg reference VM (Task D2) — PUTC/RESULT/EXIT land in the correct arena offsets

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 19 |
| Active scenarios | 19 |
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

- Canonical SPipe generation for source `6d9c2ded6cd93ed273da89c2df74c7de667463881da2b00c6b76e6044fb42d90`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `6d9c2ded6cd93ed273da89c2df74c7de667463881da2b00c6b76e6044fb42d90`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `6d9c2ded6cd93ed273da89c2df74c7de667463881da2b00c6b76e6044fb42d90`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/01_unit/lib/svmg/ref_vm_spec.spl
mirror: doc/06_spec/01_unit/lib/svmg/ref_vm_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/lib/svmg/ref_vm_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/lib/svmg/ref_vm_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/lib/svmg/ref_vm_spec.spl:30:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'adds two integers and records the result' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/svmg/ref_vm_spec.spl:45:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'computes SUB/MUL/DIV/REM correctly (10, 3)' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/svmg/ref_vm_spec.spl:68:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'computes bitwise AND/OR/XOR/SHL/SHR' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
