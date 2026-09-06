# Conformance Suite Specification

> Tests covering svmg conformance (Task D3) — control / misc, svmg conformance (Task D3) — stack ops, svmg conformance (Task D3) — integer arithmetic, svmg conformance (Task D3) — float arithmetic, svmg conformance (Task D3) — bitwise, svmg conformance (Task D3) — integer comparisons, svmg conformance (Task D3) — float comparisons, svmg conformance (Task D3) — memory, svmg conformance (Task D3) — control flow, svmg conformance (Task D3) — SYS_* and thread-id opcodes, svmg conformance (Task D3) — traps (both kinds), svmg conformance (Task D3) — step budget, svmg conformance (Task D3) — design §4.4 lowered-subset patterns, svmg conformance (Task D3) — table coverage (meta).

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 61 | 61 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Conformance Suite Specification

## Scenarios

### svmg conformance (Task D3) — control / misc

#### NOP is a no-op that falls through to the next instruction

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- NOP is a no-op that falls through to the next instruction


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("NOP is a no-op that falls through to the next instruction")
_check("nop_passthrough")
```

</details>

#### HALT writes the exit sentinel with its immediate code and no records

- HALT writes the exit sentinel with its immediate code and no records


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("HALT writes the exit sentinel with its immediate code and no records")
_check("halt_with_code")
```

</details>

#### explicit TRAP opcode writes its immediate code as the trap value

- explicit TRAP opcode writes its immediate code as the trap value


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("explicit TRAP opcode writes its immediate code as the trap value")
_check("trap_explicit")
```

</details>

### svmg conformance (Task D3) — stack ops

#### PUSHI pushes a negative i32 correctly

- PUSHI pushes a negative i32 correctly


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("PUSHI pushes a negative i32 correctly")
_check("pushi_negative")
```

</details>

#### PUSHF pushes the f32 bit pattern of a decimal literal

- PUSHF pushes the f32 bit pattern of a decimal literal


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("PUSHF pushes the f32 bit pattern of a decimal literal")
_check("pushf_literal")
```

</details>

#### DUP duplicates the top of stack

- DUP duplicates the top of stack


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("DUP duplicates the top of stack")
_check("dup_doubles")
```

</details>

#### DROP discards the top of stack

- DROP discards the top of stack


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("DROP discards the top of stack")
_check("drop_discards_top")
```

</details>

#### SWAP reorders the top two stack slots

- SWAP reorders the top two stack slots


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("SWAP reorders the top two stack slots")
_check("swap_reorders")
```

</details>

### svmg conformance (Task D3) — integer arithmetic

#### ADD

- ADD


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("ADD")
_check("add")
```

</details>

#### SUB

- SUB


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("SUB")
_check("sub")
```

</details>

#### MUL

- MUL


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("MUL")
_check("mul")
```

</details>

#### DIV

- DIV


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("DIV")
_check("div")
```

</details>

#### REM

- REM


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("REM")
_check("rem")
```

</details>

### svmg conformance (Task D3) — float arithmetic

#### FADD

- FADD


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("FADD")
_check("fadd")
```

</details>

#### FSUB

- FSUB


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("FSUB")
_check("fsub")
```

</details>

#### FMUL

- FMUL


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("FMUL")
_check("fmul")
```

</details>

#### FDIV

- FDIV


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("FDIV")
_check("fdiv")
```

</details>

### svmg conformance (Task D3) — bitwise

#### AND

- AND


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("AND")
_check("bitwise_and")
```

</details>

#### OR

- OR


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("OR")
_check("bitwise_or")
```

</details>

#### XOR

- XOR


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("XOR")
_check("bitwise_xor")
```

</details>

#### SHL

- SHL


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("SHL")
_check("shift_left")
```

</details>

#### SHR is logical (zero-fill)

- SHR is logical (zero-fill)


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("SHR is logical (zero-fill)")
_check("shift_right_logical")
```

</details>

#### SAR is arithmetic (sign-preserving)

- SAR is arithmetic (sign-preserving)


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("SAR is arithmetic (sign-preserving)")
_check("shift_right_arithmetic")
```

</details>

### svmg conformance (Task D3) — integer comparisons

#### EQ

- EQ


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("EQ")
_check("cmp_eq")
```

</details>

#### NE

- NE


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("NE")
_check("cmp_ne")
```

</details>

#### LT

- LT


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("LT")
_check("cmp_lt")
```

</details>

#### LE

- LE


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("LE")
_check("cmp_le")
```

</details>

#### GT

- GT


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("GT")
_check("cmp_gt")
```

</details>

#### GE

- GE


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("GE")
_check("cmp_ge")
```

</details>

### svmg conformance (Task D3) — float comparisons

#### FEQ

- FEQ


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("FEQ")
_check("fcmp_eq")
```

</details>

#### FNE

- FNE


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("FNE")
_check("fcmp_ne")
```

</details>

#### FLT

- FLT


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("FLT")
_check("fcmp_lt")
```

</details>

#### FLE

- FLE


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("FLE")
_check("fcmp_le")
```

</details>

#### FGT

- FGT


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("FGT")
_check("fcmp_gt")
```

</details>

#### FGE

- FGE


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("FGE")
_check("fcmp_ge")
```

</details>

### svmg conformance (Task D3) — memory

#### STORE32 then LOAD32 round-trips a word

- STORE32 then LOAD32 round-trips a word


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("STORE32 then LOAD32 round-trips a word")
_check("mem_store_load_word")
```

</details>

#### STORE8 then LOAD8 round-trips a byte

- STORE8 then LOAD8 round-trips a byte


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("STORE8 then LOAD8 round-trips a byte")
_check("mem_store_load_byte")
```

</details>

### svmg conformance (Task D3) — control flow

#### JMP skips dead code

- JMP skips dead code


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("JMP skips dead code")
_check("jmp_skips_dead_code")
```

</details>

#### JZ takes the zero branch

- JZ takes the zero branch


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("JZ takes the zero branch")
_check("jz_takes_zero_branch")
```

</details>

#### JNZ takes the nonzero branch

- JNZ takes the nonzero branch


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("JNZ takes the nonzero branch")
_check("jnz_takes_nonzero_branch")
```

</details>

#### CALL/RET runs a subroutine and returns to the caller

- CALL/RET runs a subroutine and returns to the caller


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("CALL/RET runs a subroutine and returns to the caller")
_check("call_ret_subroutine_double")
```

</details>

#### RET with an empty call stack exits cleanly (top-level RET)

- RET with an empty call stack exits cleanly (top-level RET)


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("RET with an empty call stack exits cleanly (top-level RET)")
_check("ret_at_top_level_exits")
```

</details>

### svmg conformance (Task D3) — SYS_* and thread-id opcodes

#### SYS_PUTC bytes land in the LOG ring

- SYS_PUTC bytes land in the LOG ring


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("SYS_PUTC bytes land in the LOG ring")
_check("sys_putc_log_text")
```

</details>

#### SYS_EXIT pops its code and writes the exit sentinel

- SYS_EXIT pops its code and writes the exit sentinel


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("SYS_EXIT pops its code and writes the exit sentinel")
_check("sys_exit_writes_sentinel")
```

</details>

#### SYS_RESULT records pass=0 correctly

- SYS_RESULT records pass=0 correctly


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("SYS_RESULT records pass=0 correctly")
_check("sys_result_records_pass_and_value")
```

</details>

#### TID is always 0 on the single-threaded host

- TID is always 0 on the single-threaded host


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("TID is always 0 on the single-threaded host")
_check("tid_is_zero")
```

</details>

#### NTID is always 1 on the single-threaded host

- NTID is always 1 on the single-threaded host


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("NTID is always 1 on the single-threaded host")
_check("ntid_is_one")
```

</details>

#### PARFOR falls through to the fanned body executed once

- PARFOR falls through to the fanned body executed once


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("PARFOR falls through to the fanned body executed once")
_check("parfor_falls_through")
```

</details>

### svmg conformance (Task D3) — traps (both kinds)

#### bounds trap: LOAD32 out of bounds

- bounds trap: LOAD32 out of bounds


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("bounds trap: LOAD32 out of bounds")
_check("trap_bounds_load32_oob")
```

</details>

#### bounds trap: STORE8 with a negative offset

- bounds trap: STORE8 with a negative offset


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("bounds trap: STORE8 with a negative offset")
_check("trap_bounds_store8_negative_offset")
```

</details>

#### div-by-zero trap: DIV

- div-by-zero trap: DIV


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("div-by-zero trap: DIV")
_check("trap_div0_on_div")
```

</details>

#### div-by-zero trap: REM

- div-by-zero trap: REM


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("div-by-zero trap: REM")
_check("trap_div0_on_rem")
```

</details>

### svmg conformance (Task D3) — step budget

#### exhausts the step budget and writes SENTINEL_TIMEOUT (0xDEAD0000)

- exhausts the step budget and writes SENTINEL_TIMEOUT (0xDEAD0000)


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("exhausts the step budget and writes SENTINEL_TIMEOUT (0xDEAD0000)")
_check("budget_exhaustion_timeout")
# Also pin the exact step count consumed, independent of _check_vector
# (which does not compare steps_used).
val bytes = svmg_asm("NOP\nJMP -4")
val result = assemble_and_run(bytes, 10, 0)
assert_equal(result.steps_used, 10)
```

</details>

### svmg conformance (Task D3) — design §4.4 lowered-subset patterns

#### if/elif/else lowers to JZ/JMP chains and takes the elif branch

- if/elif/else lowers to JZ/JMP chains and takes the elif branch


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("if/elif/else lowers to JZ/JMP chains and takes the elif branch")
_check("pattern_if_elif_else")
```

</details>

<details>
<summary>Advanced: a bounded while-style loop (stack-carried counter) runs to completion</summary>

#### a bounded while-style loop (stack-carried counter) runs to completion

- a bounded while-style loop (stack-carried counter) runs to completion


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("a bounded while-style loop (stack-carried counter) runs to completion")
_check("pattern_while_loop")
```

</details>


</details>

<details>
<summary>Advanced: a bounded for-loop with sum/i lowered into the DATA region sums 0..4</summary>

#### a bounded for-loop with sum/i lowered into the DATA region sums 0..4

- a bounded for-loop with sum/i lowered into the DATA region sums 0..4


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("a bounded for-loop with sum/i lowered into the DATA region sums 0..4")
_check("pattern_bounded_for_sum_with_array")
```

</details>


</details>

#### a non-recursive fn call (square via CALL/RET) computes correctly

- a non-recursive fn call (square via CALL/RET) computes correctly


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("a non-recursive fn call (square via CALL/RET) computes correctly")
_check("pattern_nonrecursive_fn_call_square")
```

</details>

#### print of a string literal lowers to a PUTC-per-byte sequence

- print of a string literal lowers to a PUTC-per-byte sequence


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("print of a string literal lowers to a PUTC-per-byte sequence")
_check("pattern_print_string_literal")
```

</details>

#### expect(x).to_equal(y) lowers to EQ + SYS_RESULT(pass, value)

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("expect(x).to_equal(y) lowers to EQ + SYS_RESULT(pass, value)")
_check("pattern_expect_to_equal")
```

</details>

### svmg conformance (Task D3) — table coverage (meta)

#### the table has at least 40 vectors

- the table has at least 40 vectors


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("the table has at least 40 vectors")
assert_true(all_vectors().len() >= 40)
```

</details>

#### every one of the 50 opcodes in opcodes.spl appears in at least one vector's source

- every one of the 50 opcodes in opcodes.spl appears in at least one vector's source


<details>
<summary>Executable SSpec</summary>

Runnable source: 23 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("every one of the 50 opcodes in opcodes.spl appears in at least one vector's source")
val vectors = all_vectors()
for mnemonic in all_mnemonics():
    var found = false
    for vec in vectors:
        # Match on a token boundary (mnemonic followed by newline, space,
        # or end of string) so e.g. "JZ" doesn't false-match "JZ" inside
        # a longer token -- the opcode table has no overlapping-prefix
        # mnemonics today, but this keeps the check honest if one is
        # ever added.
        if vec.source == mnemonic:
            found = true
        elif vec.source.starts_with(mnemonic + " ") or vec.source.starts_with(mnemonic + "\n"):
            found = true
        elif vec.source.contains("\n" + mnemonic + " ") or vec.source.contains("\n" + mnemonic + "\n"):
            found = true
        elif vec.source.ends_with("\n" + mnemonic):
            # No-operand mnemonic as the LAST instruction (no trailing
            # newline after it), e.g. a program that ends in bare
            # "...\nSYS_EXIT" or "...\nRET".
            found = true
    assert_true(found)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/02_integration/svmg/conformance/conformance_suite_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering svmg conformance (Task D3) — control / misc, svmg conformance (Task D3) — stack ops, svmg conformance (Task D3) — integer arithmetic, svmg conformance (Task D3) — float arithmetic, svmg conformance (Task D3) — bitwise, svmg conformance (Task D3) — integer comparisons, svmg conformance (Task D3) — float comparisons, svmg conformance (Task D3) — memory, svmg conformance (Task D3) — control flow, svmg conformance (Task D3) — SYS_* and thread-id opcodes, svmg conformance (Task D3) — traps (both kinds), svmg conformance (Task D3) — step budget, svmg conformance (Task D3) — design §4.4 lowered-subset patterns, svmg conformance (Task D3) — table coverage (meta).
- svmg conformance (Task D3) — control / misc
- svmg conformance (Task D3) — stack ops
- svmg conformance (Task D3) — integer arithmetic
- svmg conformance (Task D3) — float arithmetic
- svmg conformance (Task D3) — bitwise
- svmg conformance (Task D3) — integer comparisons
- svmg conformance (Task D3) — float comparisons
- svmg conformance (Task D3) — memory
- svmg conformance (Task D3) — control flow
- svmg conformance (Task D3) — SYS_* and thread-id opcodes
- svmg conformance (Task D3) — traps (both kinds)
- svmg conformance (Task D3) — step budget
- svmg conformance (Task D3) — design §4.4 lowered-subset patterns
- svmg conformance (Task D3) — table coverage (meta)

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 61 |
| Active scenarios | 61 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-INTEGRATION`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `59d5047c1b9960faf5a78ca4c4f7712fa41c0e6ec7c5d09df1e04702839c1865`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `59d5047c1b9960faf5a78ca4c4f7712fa41c0e6ec7c5d09df1e04702839c1865`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `59d5047c1b9960faf5a78ca4c4f7712fa41c0e6ec7c5d09df1e04702839c1865`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/02_integration/svmg/conformance/conformance_suite_spec.spl
mirror: doc/06_spec/02_integration/svmg/conformance/conformance_suite_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/02_integration/svmg/conformance/conformance_suite_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/02_integration/svmg/conformance/conformance_suite_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/02_integration/svmg/conformance/conformance_suite_spec.spl:53:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'NOP is a no-op that falls through to the next instruction' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/02_integration/svmg/conformance/conformance_suite_spec.spl:57:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'HALT writes the exit sentinel with its immediate code and no records' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/02_integration/svmg/conformance/conformance_suite_spec.spl:61:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'explicit TRAP opcode writes its immediate code as the trap value' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
