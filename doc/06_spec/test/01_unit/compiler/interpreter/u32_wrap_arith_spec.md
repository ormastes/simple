# u32 / Unsigned Integer Wrap Arithmetic Specification

> Regression test for the bug filed at `doc/08_tracking/bug/interpreter_u32_wrap_subtraction_2026-05-01.md`, where the Rust seed interpreter held all integer values as `Value::Int(i64)` with no width tag, so unsigned arithmetic on `u32`-typed expressions did not wrap modulo 2^32. The classic LZMA range-coder mask `val mask: u32 = 0u32 - (code >> 31u32)` produced `-1` instead of `0xFFFFFFFF`.

<!-- sdn-diagram:id=u32_wrap_arith_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=u32_wrap_arith_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

u32_wrap_arith_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=u32_wrap_arith_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

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
| Updated | 2026-06-01 |
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

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val r: u32 = 0u32 - 1u32
expect(r == 0xFFFFFFFFu32).to_equal(true)
```

</details>

#### wraps subtraction (variable lhs): mask idiom

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val code: u32 = 0x80000000u32
val mask: u32 = 0u32 - (code >> 31u32)
expect(mask == 0xFFFFFFFFu32).to_equal(true)
```

</details>

#### wraps subtraction with zero high-bit: mask idiom

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val code: u32 = 0x12345678u32
val mask: u32 = 0u32 - (code >> 31u32)
expect(mask == 0u32).to_equal(true)
```

</details>

#### wraps addition: 0xFFFFFFFFu32 + 1u32 == 0u32

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val r: u32 = 0xFFFFFFFFu32 + 1u32
expect(r == 0u32).to_equal(true)
```

</details>

#### wraps multiplication: 0xFFFFu32 * 0x10001u32 == 0xFFFFu32 (low 32 bits)

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# 0xFFFF * 0x10001 = 0xFFFF0000 + 0xFFFF = 0xFFFFFFFF (no wrap needed)
val r: u32 = 0xFFFFu32 * 0x10001u32
expect(r == 0xFFFFFFFFu32).to_equal(true)
```

</details>

#### wraps multiplication overflow: 0x10000u32 * 0x10000u32 == 0u32

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val r: u32 = 0x10000u32 * 0x10000u32
expect(r == 0u32).to_equal(true)
```

</details>

### u8 / u16 wrap arithmetic

#### wraps u8 subtraction: 0u8 - 1u8 == 0xFFu8

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val r: u8 = 0u8 - 1u8
expect(r == 0xFFu8).to_equal(true)
```

</details>

#### wraps u16 subtraction: 0u16 - 1u16 == 0xFFFFu16

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val r: u16 = 0u16 - 1u16
expect(r == 0xFFFFu16).to_equal(true)
```

</details>

#### wraps u8 addition overflow

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val r: u8 = 0xFFu8 + 1u8
expect(r == 0u8).to_equal(true)
```

</details>

### u64 wrap arithmetic

#### wraps u64 subtraction: 0u64 - 1u64 == 0xFFFFFFFFFFFFFFFFu64

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val r: u64 = 0u64 - 1u64
expect(r == 0xFFFFFFFFFFFFFFFFu64).to_equal(true)
```

</details>

#### wraps u64 addition overflow

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val r: u64 = 0xFFFFFFFFFFFFFFFFu64 + 1u64
expect(r == 0u64).to_equal(true)
```

</details>

#### shifts u64 function parameters logically, not arithmetically

1. fn shr param
2. fn shr local
   - Expected: shr_param(0xCBBB9D5DC1059ED8u64, 28u64) == 0xCBBB9D5DCu64 is true
   - Expected: shr_local() == 0xCBBB9D5DCu64 is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
fn shr_param(x: u64, n: u64) -> u64:
    x >> n

fn shr_local() -> u64:
    val x: u64 = 0xCBBB9D5DC1059ED8u64
    x >> 28u64

expect(shr_param(0xCBBB9D5DC1059ED8u64, 28u64) == 0xCBBB9D5DCu64).to_equal(true)
expect(shr_local() == 0xCBBB9D5DCu64).to_equal(true)
```

</details>

### signed integer arithmetic (no regression)

#### i64 subtraction stays signed: 0 - 1 == -1

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val r: i64 = 0 - 1
expect(r == -1).to_equal(true)
```

</details>

#### i32 cast keeps signed semantics: (-1 as i32) is still -1

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val n: i64 = -1
val r: i32 = n.to_i32()
expect(r == -1).to_equal(true)
```

</details>

#### mixed i64 + u32 is governed by u32 wrap (UInt-wins)

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Cross-variant: when one operand is UInt, the wrap-width applies.
# This documents the chosen semantics; if/when a stricter type rule
# rejects mixed arithmetic, this spec should be updated together.
val u: u32 = 1u32
val s: i64 = 0
val r: u32 = (s.to_u32()) - u
expect(r == 0xFFFFFFFFu32).to_equal(true)
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
