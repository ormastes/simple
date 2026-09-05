# u32 / Unsigned Integer Wrap Arithmetic Specification

> Regression test for the bug filed at `doc/08_tracking/bug/interpreter_u32_wrap_subtraction_2026-05-01.md`, where the Rust seed interpreter held all integer values as `Value::Int(i64)` with no width tag, so unsigned arithmetic on `u32`-typed expressions did not wrap modulo 2^32. The classic LZMA range-coder mask `val mask: u32 = 0u32 - (code >> 31u32)` produced `-1` instead of `0xFFFFFFFF`.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 15 | 15 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# u32 / Unsigned Integer Wrap Arithmetic Specification

Regression test for the bug filed at `doc/08_tracking/bug/interpreter_u32_wrap_subtraction_2026-05-01.md`, where the Rust seed interpreter held all integer values as `Value::Int(i64)` with no width tag, so unsigned arithmetic on `u32`-typed expressions did not wrap modulo 2^32. The classic LZMA range-coder mask `val mask: u32 = 0u32 - (code >> 31u32)` produced `-1` instead of `0xFFFFFFFF`.

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #INTERP-U32-WRAP |
| Category | Interpreter |
| Difficulty | 2/5 |
| Status | Regression |
| Source | `test/01_unit/compiler/interpreter/u32_wrap_arith_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Regression test for the bug filed at
`doc/08_tracking/bug/interpreter_u32_wrap_subtraction_2026-05-01.md`,
where the Rust seed interpreter held all integer values as `Value::Int(i64)`
with no width tag, so unsigned arithmetic on `u32`-typed expressions did not
wrap modulo 2^32. The classic LZMA range-coder mask
`val mask: u32 = 0u32 - (code >> 31u32)` produced `-1` instead of
`0xFFFFFFFF`.

The fix introduces a `Value::UInt { value: u64, width: u8 }` variant carried
through arithmetic ops in `src/compiler_rust/compiler/src/interpreter/expr/
ops.rs`. Add/Sub/Mul/Neg apply `wrapping_*` at the operand width when at
least one side is `Value::UInt`; bitwise/shift ops preserve UInt-ness so
chains like `(code >> 31u32)` keep their u32 type into the surrounding
subtraction.

This spec exercises:
- u32 subtraction wrap (the LZMA range-coder idiom)
- u32 addition overflow wrap
- u32 multiplication overflow wrap
- u32 negation wrap
- u8 / u16 wrap at narrower widths
- u64 wrap (already worked before by accident — pinned here so a future
  refactor doesn't drop it)

## Scenarios

### u32 wrap arithmetic

#### wraps subtraction: 0u32 - 1u32 == 0xFFFFFFFFu32

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- wraps subtraction: 0u32 - 1u32 == 0xFFFFFFFFu32
   - Expected: r equals `0xFFFFFFFFu32`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("wraps subtraction: 0u32 - 1u32 == 0xFFFFFFFFu32")
val r: u32 = 0u32 - 1u32
expect(r).to_equal(0xFFFFFFFFu32)
```

</details>

#### wraps subtraction (variable lhs): mask idiom

- wraps subtraction (variable lhs): mask idiom
   - Expected: mask equals `0xFFFFFFFFu32`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("wraps subtraction (variable lhs): mask idiom")
val code: u32 = 0x80000000u32
val mask: u32 = 0u32 - (code >> 31u32)
expect(mask).to_equal(0xFFFFFFFFu32)
```

</details>

#### wraps subtraction with zero high-bit: mask idiom

- wraps subtraction with zero high-bit: mask idiom
   - Expected: mask equals `0u32`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("wraps subtraction with zero high-bit: mask idiom")
val code: u32 = 0x12345678u32
val mask: u32 = 0u32 - (code >> 31u32)
expect(mask).to_equal(0u32)
```

</details>

#### wraps addition: 0xFFFFFFFFu32 + 1u32 == 0u32

- wraps addition: 0xFFFFFFFFu32 + 1u32 == 0u32
   - Expected: r equals `0u32`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("wraps addition: 0xFFFFFFFFu32 + 1u32 == 0u32")
val r: u32 = 0xFFFFFFFFu32 + 1u32
expect(r).to_equal(0u32)
```

</details>

#### wraps multiplication: 0xFFFFu32 * 0x10001u32 == 0xFFFFu32 (low 32 bits)

- wraps multiplication: 0xFFFFu32 * 0x10001u32 == 0xFFFFu32 (low 32 bits)
   - Expected: r equals `0xFFFFFFFFu32`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("wraps multiplication: 0xFFFFu32 * 0x10001u32 == 0xFFFFu32 (low 32 bits)")
# 0xFFFF * 0x10001 = 0xFFFF0000 + 0xFFFF = 0xFFFFFFFF (no wrap needed)
val r: u32 = 0xFFFFu32 * 0x10001u32
expect(r).to_equal(0xFFFFFFFFu32)
```

</details>

#### wraps multiplication overflow: 0x10000u32 * 0x10000u32 == 0u32

- wraps multiplication overflow: 0x10000u32 * 0x10000u32 == 0u32
   - Expected: r equals `0u32`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("wraps multiplication overflow: 0x10000u32 * 0x10000u32 == 0u32")
val r: u32 = 0x10000u32 * 0x10000u32
expect(r).to_equal(0u32)
```

</details>

### u8 / u16 wrap arithmetic

#### wraps u8 subtraction: 0u8 - 1u8 == 0xFFu8

- wraps u8 subtraction: 0u8 - 1u8 == 0xFFu8
   - Expected: r equals `0xFFu8`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("wraps u8 subtraction: 0u8 - 1u8 == 0xFFu8")
val r: u8 = 0u8 - 1u8
expect(r).to_equal(0xFFu8)
```

</details>

#### wraps u16 subtraction: 0u16 - 1u16 == 0xFFFFu16

- wraps u16 subtraction: 0u16 - 1u16 == 0xFFFFu16
   - Expected: r equals `0xFFFFu16`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("wraps u16 subtraction: 0u16 - 1u16 == 0xFFFFu16")
val r: u16 = 0u16 - 1u16
expect(r).to_equal(0xFFFFu16)
```

</details>

#### wraps u8 addition overflow

- wraps u8 addition overflow
   - Expected: r equals `0u8`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("wraps u8 addition overflow")
val r: u8 = 0xFFu8 + 1u8
expect(r).to_equal(0u8)
```

</details>

### u64 wrap arithmetic

#### wraps u64 subtraction: 0u64 - 1u64 == 0xFFFFFFFFFFFFFFFFu64

- wraps u64 subtraction: 0u64 - 1u64 == 0xFFFFFFFFFFFFFFFFu64
   - Expected: r equals `0xFFFFFFFFFFFFFFFFu64`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("wraps u64 subtraction: 0u64 - 1u64 == 0xFFFFFFFFFFFFFFFFu64")
val r: u64 = 0u64 - 1u64
expect(r).to_equal(0xFFFFFFFFFFFFFFFFu64)
```

</details>

#### wraps u64 addition overflow

- wraps u64 addition overflow
   - Expected: r equals `0u64`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("wraps u64 addition overflow")
val r: u64 = 0xFFFFFFFFFFFFFFFFu64 + 1u64
expect(r).to_equal(0u64)
```

</details>

#### shifts u64 function parameters logically, not arithmetically

- shifts u64 function parameters logically, not arithmetically
   - Expected: shr_param(0xCBBB9D5DC1059ED8u64, 28u64) equals `0xCBBB9D5DCu64`
   - Expected: shr_local() equals `0xCBBB9D5DCu64`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("shifts u64 function parameters logically, not arithmetically")
fn shr_param(x: u64, n: u64) -> u64:
    x >> n

fn shr_local() -> u64:
    val x: u64 = 0xCBBB9D5DC1059ED8u64
    x >> 28u64

expect(shr_param(0xCBBB9D5DC1059ED8u64, 28u64)).to_equal(0xCBBB9D5DCu64)
expect(shr_local()).to_equal(0xCBBB9D5DCu64)
```

</details>

### signed integer arithmetic (no regression)

#### i64 subtraction stays signed: 0 - 1 == -1

- i64 subtraction stays signed: 0 - 1 == -1
   - Expected: r equals `-1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("i64 subtraction stays signed: 0 - 1 == -1")
val r: i64 = 0 - 1
expect(r).to_equal(-1)
```

</details>

#### i32 cast keeps signed semantics: (-1 as i32) is still -1

- i32 cast keeps signed semantics: (-1 as i32) is still -1
   - Expected: r equals `-1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("i32 cast keeps signed semantics: (-1 as i32) is still -1")
val n: i64 = -1
val r: i32 = n.to_i32()
expect(r).to_equal(-1)
```

</details>

#### mixed i64 + u32 is governed by u32 wrap (UInt-wins)

- mixed i64 + u32 is governed by u32 wrap (UInt-wins)
   - Expected: r equals `0xFFFFFFFFu32`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("mixed i64 + u32 is governed by u32 wrap (UInt-wins)")
# Cross-variant: when one operand is UInt, the wrap-width applies.
# This documents the chosen semantics; if/when a stricter type rule
# rejects mixed arithmetic, this spec should be updated together.
val u: u32 = 1u32
val s: i64 = 0
val r: u32 = (s.to_u32()) - u
expect(r).to_equal(0xFFFFFFFFu32)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 15 |
| Active scenarios | 15 |
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

- Canonical SPipe generation for source `db0328e9257af0ac410493e64162d11513f12b7f71356695a33db699a458488a`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `db0328e9257af0ac410493e64162d11513f12b7f71356695a33db699a458488a`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `db0328e9257af0ac410493e64162d11513f12b7f71356695a33db699a458488a`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **88/100**; effective score: **88/100**; blockers: **0**.

SSpec documentization score: 88/100
source: test/01_unit/compiler/interpreter/u32_wrap_arith_spec.spl
mirror: doc/06_spec/01_unit/compiler/interpreter/u32_wrap_arith_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=80
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/compiler/interpreter/u32_wrap_arith_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/compiler/interpreter/u32_wrap_arith_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/compiler/interpreter/u32_wrap_arith_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-20): 2 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/compiler/interpreter/u32_wrap_arith_spec.spl:46:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'wraps subtraction: 0u32 - 1u32 == 0xFFFFFFFFu32' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/interpreter/u32_wrap_arith_spec.spl:52:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'wraps subtraction (variable lhs): mask idiom' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/interpreter/u32_wrap_arith_spec.spl:59:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'wraps subtraction with zero high-bit: mask idiom' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
