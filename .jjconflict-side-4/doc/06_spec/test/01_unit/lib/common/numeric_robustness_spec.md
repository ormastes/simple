# Numeric Robustness Specification Tests

> Tests for the numeric robustness system defined in `doc/06_spec/numeric_robustness.md`. Verifies checked arithmetic, fault detection, saturating operations, robust float comparison, tiny canonicalization, and PyTorch interop helpers.

<!-- sdn-diagram:id=numeric_robustness_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=numeric_robustness_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

numeric_robustness_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=numeric_robustness_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 119 | 119 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Numeric Robustness Specification Tests

Tests for the numeric robustness system defined in `doc/06_spec/numeric_robustness.md`. Verifies checked arithmetic, fault detection, saturating operations, robust float comparison, tiny canonicalization, and PyTorch interop helpers.

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #NR-001 to #NR-010 |
| Category | Stdlib |
| Status | In Progress |
| Source | `test/01_unit/lib/common/numeric_robustness_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests for the numeric robustness system defined in `doc/06_spec/numeric_robustness.md`.
Verifies checked arithmetic, fault detection, saturating operations,
robust float comparison, tiny canonicalization, and PyTorch interop helpers.

## Key Concepts

| Concept | Description |
|---------|-------------|
| CheckedF64 | Float result that may contain a fault (NaN, Inf, DivByZero, etc.) |
| CheckedI64 | Integer result that may contain a fault (DivByZero, Overflow, etc.) |
| Fault | Text tag identifying the numeric hazard that occurred |
| Saturating | Arithmetic that clamps to min/max on overflow instead of faulting |
| Dual tolerance | Float comparison using both relative and absolute tolerance |
| Tiny canonicalization | Flushing subnormal/tiny values to signed zero |

## Related Specifications

- [Numeric Robustness Spec](../../../doc/06_spec/numeric_robustness.md)

## Scenarios

### Checked Float Division

#### normal division

#### divides two positive numbers

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val r = checked_div_f64(10.0, 2.0)
expect(is_ok_f64(r)).to_equal(true)
expect(r.value).to_equal(5.0)
```

</details>

#### divides negative by positive

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val r = checked_div_f64(-10.0, 2.0)
expect(is_ok_f64(r)).to_equal(true)
expect(r.value).to_equal(-5.0)
```

</details>

#### divides positive by negative

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val r = checked_div_f64(10.0, -2.0)
expect(is_ok_f64(r)).to_equal(true)
expect(r.value).to_equal(-5.0)
```

</details>

#### divides zero by nonzero

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val r = checked_div_f64(0.0, 5.0)
expect(is_ok_f64(r)).to_equal(true)
expect(r.value).to_equal(0.0)
```

</details>

#### divides with fractional result

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val r = checked_div_f64(1.0, 3.0)
expect(is_ok_f64(r)).to_equal(true)
val close = float_eq_robust(r.value, 0.333333, 1e-4, 1e-6)
expect(close).to_equal(true)
```

</details>

#### division by zero

#### detects 0/0 as NaN fault

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val r = checked_div_f64(0.0, 0.0)
expect(is_fault_f64(r)).to_equal(true)
expect(r.fault).to_equal(FAULT_NAN)
```

</details>

#### detects positive/0 as +Inf fault

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val r = checked_div_f64(1.0, 0.0)
expect(is_fault_f64(r)).to_equal(true)
expect(r.fault).to_equal(FAULT_POSINF)
```

</details>

#### detects large positive/0 as +Inf fault

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val r = checked_div_f64(999999.0, 0.0)
expect(is_fault_f64(r)).to_equal(true)
expect(r.fault).to_equal(FAULT_POSINF)
```

</details>

#### detects negative/0 as -Inf fault

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val r = checked_div_f64(-1.0, 0.0)
expect(is_fault_f64(r)).to_equal(true)
expect(r.fault).to_equal(FAULT_NEGINF)
```

</details>

#### detects large negative/0 as -Inf fault

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val r = checked_div_f64(-999999.0, 0.0)
expect(is_fault_f64(r)).to_equal(true)
expect(r.fault).to_equal(FAULT_NEGINF)
```

</details>

### Checked Float Domain Functions

#### checked sqrt

#### computes sqrt of positive number

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val r = checked_sqrt_f64(4.0)
expect(is_ok_f64(r)).to_equal(true)
val close = float_eq_robust(r.value, 2.0, 1e-9, 1e-12)
expect(close).to_equal(true)
```

</details>

#### computes sqrt of 1

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val r = checked_sqrt_f64(1.0)
expect(is_ok_f64(r)).to_equal(true)
val close = float_eq_robust(r.value, 1.0, 1e-9, 1e-12)
expect(close).to_equal(true)
```

</details>

#### computes sqrt of zero

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val r = checked_sqrt_f64(0.0)
expect(is_ok_f64(r)).to_equal(true)
expect(r.value).to_equal(0.0)
```

</details>

#### faults on negative input

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val r = checked_sqrt_f64(-1.0)
expect(is_fault_f64(r)).to_equal(true)
expect(r.fault).to_equal(FAULT_INVALIDOP)
```

</details>

#### faults on large negative input

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val r = checked_sqrt_f64(-100.0)
expect(is_fault_f64(r)).to_equal(true)
expect(r.fault).to_equal(FAULT_INVALIDOP)
```

</details>

#### checked log

#### computes log of positive number

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val r = checked_log_f64(1.0)
expect(is_ok_f64(r)).to_equal(true)
val close = float_eq_robust(r.value, 0.0, 1e-6, 1e-9)
expect(close).to_equal(true)
```

</details>

#### computes log of e (approximately 1)

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val r = checked_log_f64(2.718281828)
expect(is_ok_f64(r)).to_equal(true)
val close = float_eq_robust(r.value, 1.0, 1e-4, 1e-6)
expect(close).to_equal(true)
```

</details>

#### faults on negative input

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val r = checked_log_f64(-1.0)
expect(is_fault_f64(r)).to_equal(true)
expect(r.fault).to_equal(FAULT_INVALIDOP)
```

</details>

#### faults on zero (log 0 = -Inf)

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val r = checked_log_f64(0.0)
expect(is_fault_f64(r)).to_equal(true)
expect(r.fault).to_equal(FAULT_NEGINF)
```

</details>

### Checked Integer Division

#### normal division

#### divides two positive numbers

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val r = checked_div_i64(10, 2)
expect(is_ok_i64(r)).to_equal(true)
expect(r.value).to_equal(5)
```

</details>

#### divides negative by positive

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val r = checked_div_i64(-10, 2)
expect(is_ok_i64(r)).to_equal(true)
expect(r.value).to_equal(-5)
```

</details>

#### divides with remainder truncated

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val r = checked_div_i64(7, 2)
expect(is_ok_i64(r)).to_equal(true)
expect(r.value).to_equal(3)
```

</details>

#### divides by 1

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val r = checked_div_i64(42, 1)
expect(is_ok_i64(r)).to_equal(true)
expect(r.value).to_equal(42)
```

</details>

#### divides zero by nonzero

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val r = checked_div_i64(0, 5)
expect(is_ok_i64(r)).to_equal(true)
expect(r.value).to_equal(0)
```

</details>

#### division by zero

#### detects division by zero

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val r = checked_div_i64(42, 0)
expect(is_fault_i64(r)).to_equal(true)
expect(r.fault).to_equal(FAULT_DIVBYZERO)
```

</details>

#### detects zero divided by zero

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val r = checked_div_i64(0, 0)
expect(is_fault_i64(r)).to_equal(true)
expect(r.fault).to_equal(FAULT_DIVBYZERO)
```

</details>

#### detects modulo by zero

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val r = checked_mod_i64(42, 0)
expect(is_fault_i64(r)).to_equal(true)
expect(r.fault).to_equal(FAULT_DIVBYZERO)
```

</details>

#### MIN_INT / -1 overflow

#### detects MIN_INT / -1 as overflow

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val r = checked_div_i64(MIN_I64, -1)
expect(is_fault_i64(r)).to_equal(true)
expect(r.fault).to_equal(FAULT_OVERFLOW)
```

</details>

#### allows MIN_INT / 1

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val r = checked_div_i64(MIN_I64, 1)
expect(is_ok_i64(r)).to_equal(true)
expect(r.value).to_equal(MIN_I64)
```

</details>

#### allows MIN_INT / 2

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val r = checked_div_i64(MIN_I64, 2)
expect(is_ok_i64(r)).to_equal(true)
```

</details>

### Checked Integer Addition

#### normal addition

#### adds two positive numbers

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val r = checked_add_i64(3, 4)
expect(is_ok_i64(r)).to_equal(true)
expect(r.value).to_equal(7)
```

</details>

#### adds positive and negative

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val r = checked_add_i64(10, -3)
expect(is_ok_i64(r)).to_equal(true)
expect(r.value).to_equal(7)
```

</details>

#### adds two negative numbers

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val r = checked_add_i64(-3, -4)
expect(is_ok_i64(r)).to_equal(true)
expect(r.value).to_equal(-7)
```

</details>

#### adds zero

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val r = checked_add_i64(42, 0)
expect(is_ok_i64(r)).to_equal(true)
expect(r.value).to_equal(42)
```

</details>

#### positive overflow

#### detects MAX + 1 overflow

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val r = checked_add_i64(MAX_I64, 1)
expect(is_fault_i64(r)).to_equal(true)
expect(r.fault).to_equal(FAULT_OVERFLOW)
```

</details>

#### detects large positive overflow

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val r = checked_add_i64(MAX_I64, MAX_I64)
expect(is_fault_i64(r)).to_equal(true)
expect(r.fault).to_equal(FAULT_OVERFLOW)
```

</details>

#### allows MAX + 0

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val r = checked_add_i64(MAX_I64, 0)
expect(is_ok_i64(r)).to_equal(true)
expect(r.value).to_equal(MAX_I64)
```

</details>

#### negative overflow

#### detects MIN - 1 overflow

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val r = checked_add_i64(MIN_I64, -1)
expect(is_fault_i64(r)).to_equal(true)
expect(r.fault).to_equal(FAULT_OVERFLOW)
```

</details>

#### allows MIN + 0

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val r = checked_add_i64(MIN_I64, 0)
expect(is_ok_i64(r)).to_equal(true)
expect(r.value).to_equal(MIN_I64)
```

</details>

#### subtraction overflow

#### normal subtraction

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val r = checked_sub_i64(10, 3)
expect(is_ok_i64(r)).to_equal(true)
expect(r.value).to_equal(7)
```

</details>

#### detects positive overflow on subtract negative

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val r = checked_sub_i64(MAX_I64, -1)
expect(is_fault_i64(r)).to_equal(true)
expect(r.fault).to_equal(FAULT_OVERFLOW)
```

</details>

#### detects negative overflow on subtract positive

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val r = checked_sub_i64(MIN_I64, 1)
expect(is_fault_i64(r)).to_equal(true)
expect(r.fault).to_equal(FAULT_OVERFLOW)
```

</details>

### Checked Integer Multiplication

#### normal multiplication

#### multiplies two small numbers

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val r = checked_mul_i64(3, 4)
expect(is_ok_i64(r)).to_equal(true)
expect(r.value).to_equal(12)
```

</details>

#### multiplies by zero

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val r = checked_mul_i64(MAX_I64, 0)
expect(is_ok_i64(r)).to_equal(true)
expect(r.value).to_equal(0)
```

</details>

#### multiplies zero by large

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val r = checked_mul_i64(0, MAX_I64)
expect(is_ok_i64(r)).to_equal(true)
expect(r.value).to_equal(0)
```

</details>

#### multiplies by one

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val r = checked_mul_i64(42, 1)
expect(is_ok_i64(r)).to_equal(true)
expect(r.value).to_equal(42)
```

</details>

#### multiplies by negative one

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val r = checked_mul_i64(42, -1)
expect(is_ok_i64(r)).to_equal(true)
expect(r.value).to_equal(-42)
```

</details>

#### overflow

#### detects MAX * 2 overflow

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val r = checked_mul_i64(MAX_I64, 2)
expect(is_fault_i64(r)).to_equal(true)
expect(r.fault).to_equal(FAULT_OVERFLOW)
```

</details>

#### detects large factor overflow

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val r = checked_mul_i64(1000000000, 10000000000)
expect(is_fault_i64(r)).to_equal(true)
expect(r.fault).to_equal(FAULT_OVERFLOW)
```

</details>

### Checked Bit Shifts

#### valid shifts

#### shifts left by small amount

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val r = checked_shl_i64(1, 3)
expect(is_ok_i64(r)).to_equal(true)
expect(r.value).to_equal(8)
```

</details>

#### shifts left by zero

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val r = checked_shl_i64(42, 0)
expect(is_ok_i64(r)).to_equal(true)
expect(r.value).to_equal(42)
```

</details>

#### shifts right by small amount

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val r = checked_shr_i64(8, 3)
expect(is_ok_i64(r)).to_equal(true)
expect(r.value).to_equal(1)
```

</details>

#### shifts left by 63 (max valid)

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val r = checked_shl_i64(1, 63)
expect(is_ok_i64(r)).to_equal(true)
```

</details>

#### invalid shifts

#### faults on shift left by 64

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val r = checked_shl_i64(1, 64)
expect(is_fault_i64(r)).to_equal(true)
expect(r.fault).to_equal(FAULT_SHIFT_RANGE)
```

</details>

#### faults on shift left by negative

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val r = checked_shl_i64(1, -1)
expect(is_fault_i64(r)).to_equal(true)
expect(r.fault).to_equal(FAULT_SHIFT_RANGE)
```

</details>

#### faults on shift right by 100

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val r = checked_shr_i64(1, 100)
expect(is_fault_i64(r)).to_equal(true)
expect(r.fault).to_equal(FAULT_SHIFT_RANGE)
```

</details>

#### faults on shift left by very large amount

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val r = checked_shl_i64(1, 1000)
expect(is_fault_i64(r)).to_equal(true)
expect(r.fault).to_equal(FAULT_SHIFT_RANGE)
```

</details>

### Saturating Arithmetic

#### saturating addition

#### adds normally when no overflow

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(saturate_add_i64(3, 4)).to_equal(7)
```

</details>

#### clamps to MAX on positive overflow

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(saturate_add_i64(MAX_I64, 1)).to_equal(MAX_I64)
```

</details>

#### clamps to MAX on large positive overflow

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(saturate_add_i64(MAX_I64, MAX_I64)).to_equal(MAX_I64)
```

</details>

#### clamps to MIN on negative overflow

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(saturate_add_i64(MIN_I64, -1)).to_equal(MIN_I64)
```

</details>

#### handles zero addend at MAX

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(saturate_add_i64(MAX_I64, 0)).to_equal(MAX_I64)
```

</details>

#### handles mixed signs (no overflow)

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(saturate_add_i64(MAX_I64, -1)).to_equal(MAX_I64 - 1)
```

</details>

#### saturating subtraction

#### subtracts normally when no overflow

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(saturate_sub_i64(10, 3)).to_equal(7)
```

</details>

#### clamps to MIN on negative overflow

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(saturate_sub_i64(MIN_I64, 1)).to_equal(MIN_I64)
```

</details>

#### clamps to MAX on positive overflow

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(saturate_sub_i64(MAX_I64, -1)).to_equal(MAX_I64)
```

</details>

#### saturating multiplication

#### multiplies normally when no overflow

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(saturate_mul_i64(3, 4)).to_equal(12)
```

</details>

#### returns zero for zero operand

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(saturate_mul_i64(MAX_I64, 0)).to_equal(0)
```

</details>

#### clamps to MAX on positive overflow

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(saturate_mul_i64(MAX_I64, 2)).to_equal(MAX_I64)
```

</details>

#### clamps to MIN on negative overflow

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(saturate_mul_i64(MAX_I64, -2)).to_equal(MIN_I64)
```

</details>

### Robust Float Comparison

#### exact equality

#### detects identical values

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(float_eq(0.0, 0.0)).to_equal(true)
```

</details>

#### detects identical integers

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(float_eq(42.0, 42.0)).to_equal(true)
```

</details>

#### detects identical negative values

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(float_eq(-1.5, -1.5)).to_equal(true)
```

</details>

#### near-zero comparison

#### treats very small difference as equal

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(float_eq_robust(0.0, 1e-15, 1e-9, 1e-12)).to_equal(true)
```

</details>

#### treats larger difference as not equal

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(float_eq_robust(0.0, 1.0, 1e-9, 1e-12)).to_equal(false)
```

</details>

#### treats small negative as close to zero

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(float_eq_robust(0.0, -1e-15, 1e-9, 1e-12)).to_equal(true)
```

</details>

#### large value comparison

#### treats close large values as equal

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val a = 1000000000.0
val b = 1000000001.0
expect(float_eq_robust(a, b, 1e-6, 1e-12)).to_equal(true)
```

</details>

#### treats distant large values as not equal

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val a = 1000000000.0
val b = 1001000000.0
expect(float_eq_robust(a, b, 1e-6, 1e-12)).to_equal(false)
```

</details>

#### clearly different values

#### detects 1 vs 2 as different

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(float_eq(1.0, 2.0)).to_equal(false)
```

</details>

#### detects positive vs negative as different

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(float_eq(1.0, -1.0)).to_equal(false)
```

</details>

#### tolerance parameters

#### wider tolerance accepts larger differences

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(float_eq_robust(1.0, 1.1, 0.2, 0.0)).to_equal(true)
```

</details>

#### tighter tolerance rejects same difference

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(float_eq_robust(1.0, 1.1, 0.01, 0.0)).to_equal(false)
```

</details>

#### absolute tolerance handles zero case

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(float_eq_robust(0.0, 0.05, 0.0, 0.1)).to_equal(true)
```

</details>

### Tiny Canonicalization

#### positive tiny values

#### flushes small positive to zero

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = canonicalize_tiny_with_eps(1e-30, 1e-20)
expect(result).to_equal(0.0)
```

</details>

#### preserves normal positive

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = canonicalize_tiny_with_eps(1.0, 1e-20)
expect(result).to_equal(1.0)
```

</details>

#### preserves value at epsilon boundary

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = canonicalize_tiny_with_eps(1e-10, 1e-20)
expect(result).to_equal(1e-10)
```

</details>

#### negative tiny values

#### flushes small negative to zero

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = canonicalize_tiny_with_eps(-1e-30, 1e-20)
expect(result).to_equal(0.0)
```

</details>

#### preserves normal negative

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = canonicalize_tiny_with_eps(-1.0, 1e-20)
expect(result).to_equal(-1.0)
```

</details>

#### zero passthrough

#### preserves exact zero

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = canonicalize_tiny_with_eps(0.0, 1e-20)
expect(result).to_equal(0.0)
```

</details>

#### custom epsilon

#### uses larger epsilon for embedded

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = canonicalize_tiny_with_eps(0.001, 0.01)
expect(result).to_equal(0.0)
```

</details>

#### preserves value above larger epsilon

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = canonicalize_tiny_with_eps(0.1, 0.01)
expect(result).to_equal(0.1)
```

</details>

### Fault Recovery and nan_to_num

#### recover_f64

#### passes through valid values

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val r = ok_f64(42.0)
expect(recover_f64(r, 0.0)).to_equal(42.0)
```

</details>

#### returns fallback on fault

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val r = fault_f64(FAULT_NAN)
expect(recover_f64(r, -1.0)).to_equal(-1.0)
```

</details>

#### returns fallback on any fault type

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val r = fault_f64(FAULT_OVERFLOW)
expect(recover_f64(r, 99.0)).to_equal(99.0)
```

</details>

#### recover_i64

#### passes through valid values

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val r = ok_i64(42)
expect(recover_i64(r, 0)).to_equal(42)
```

</details>

#### returns fallback on fault

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val r = fault_i64(FAULT_DIVBYZERO)
expect(recover_i64(r, -1)).to_equal(-1)
```

</details>

#### nan_to_num_checked (PyTorch interop)

#### passes through valid value

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val r = ok_f64(3.14)
val v = nan_to_num_checked(r, 0.0, 9999999.0, -9999999.0)
val close = float_eq_robust(v, 3.14, 1e-9, 1e-12)
expect(close).to_equal(true)
```

</details>

#### maps NaN fault to nan_val

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val r = fault_f64(FAULT_NAN)
val v = nan_to_num_checked(r, 0.0, 9999999.0, -9999999.0)
expect(v).to_equal(0.0)
```

</details>

#### maps PosInf fault to posinf_val

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val r = fault_f64(FAULT_POSINF)
val v = nan_to_num_checked(r, 0.0, 9999999.0, -9999999.0)
expect(v).to_equal(9999999.0)
```

</details>

#### maps NegInf fault to neginf_val

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val r = fault_f64(FAULT_NEGINF)
val v = nan_to_num_checked(r, 0.0, 9999999.0, -9999999.0)
expect(v).to_equal(-9999999.0)
```

</details>

#### maps DivByZero fault to nan_val

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val r = fault_f64(FAULT_DIVBYZERO)
val v = nan_to_num_checked(r, 0.0, 9999999.0, -9999999.0)
expect(v).to_equal(0.0)
```

</details>

#### nan_to_num_default

#### maps NaN to 0

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val r = fault_f64(FAULT_NAN)
expect(nan_to_num_default(r)).to_equal(0.0)
```

</details>

#### maps PosInf to 9999999

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val r = fault_f64(FAULT_POSINF)
expect(nan_to_num_default(r)).to_equal(9999999.0)
```

</details>

#### maps NegInf to -9999999

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val r = fault_f64(FAULT_NEGINF)
expect(nan_to_num_default(r)).to_equal(-9999999.0)
```

</details>

#### composition: checked -> recovery

#### recovers from division by zero

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val r = checked_div_f64(1.0, 0.0)
val v = recover_f64(r, 0.0)
expect(v).to_equal(0.0)
```

</details>

#### preserves normal division result

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val r = checked_div_f64(10.0, 2.0)
val v = recover_f64(r, 0.0)
expect(v).to_equal(5.0)
```

</details>

#### chains division and nan_to_num

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val r = checked_div_f64(0.0, 0.0)
val v = nan_to_num_default(r)
expect(v).to_equal(0.0)
```

</details>

#### chains sqrt fault recovery

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val r = checked_sqrt_f64(-4.0)
val v = nan_to_num_default(r)
expect(v).to_equal(0.0)
```

</details>

### Checked Float-to-Int Conversion

#### normal conversions

#### converts integer-valued float

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val r = checked_f64_to_i64(42.0)
expect(is_ok_i64(r)).to_equal(true)
expect(r.value).to_equal(42)
```

</details>

#### converts zero

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val r = checked_f64_to_i64(0.0)
expect(is_ok_i64(r)).to_equal(true)
expect(r.value).to_equal(0)
```

</details>

#### truncates fractional part

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val r = checked_f64_to_i64(3.7)
expect(is_ok_i64(r)).to_equal(true)
expect(r.value).to_equal(3)
```

</details>

#### converts negative

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val r = checked_f64_to_i64(-5.0)
expect(is_ok_i64(r)).to_equal(true)
expect(r.value).to_equal(-5)
```

</details>

#### out-of-range conversions

#### faults on very large positive

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val r = checked_f64_to_i64(1e19)
expect(is_fault_i64(r)).to_equal(true)
expect(r.fault).to_equal(FAULT_INVALID_CAST)
```

</details>

#### faults on very large negative

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val r = checked_f64_to_i64(-1e19)
expect(is_fault_i64(r)).to_equal(true)
expect(r.fault).to_equal(FAULT_INVALID_CAST)
```

</details>

### Checked Operation Composition

#### chained float operations

#### chains two successful divisions

- var v1 = recover f64
- var v2 = recover f64
   - Expected: v2 equals `5.0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val r1 = checked_div_f64(100.0, 5.0)
var v1 = recover_f64(r1, 0.0)
val r2 = checked_div_f64(v1, 4.0)
var v2 = recover_f64(r2, 0.0)
expect(v2).to_equal(5.0)
```

</details>

#### propagates fault from first operation

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val r1 = checked_div_f64(1.0, 0.0)
val recovered = recover_f64(r1, 0.0)
val r2 = checked_div_f64(recovered, 2.0)
expect(is_ok_f64(r2)).to_equal(true)
expect(r2.value).to_equal(0.0)
```

</details>

#### chained integer operations

#### chains add and multiply

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val r1 = checked_add_i64(10, 20)
val v1 = recover_i64(r1, 0)
val r2 = checked_mul_i64(v1, 3)
expect(is_ok_i64(r2)).to_equal(true)
expect(r2.value).to_equal(90)
```

</details>

#### detects overflow in chain

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val r1 = checked_add_i64(MAX_I64, 0)
val v1 = recover_i64(r1, 0)
val r2 = checked_add_i64(v1, 1)
expect(is_fault_i64(r2)).to_equal(true)
expect(r2.fault).to_equal(FAULT_OVERFLOW)
```

</details>

#### mixed float and int

#### converts checked float to checked int

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val r1 = checked_div_f64(10.0, 3.0)
val v = recover_f64(r1, 0.0)
val r2 = checked_f64_to_i64(v)
expect(is_ok_i64(r2)).to_equal(true)
expect(r2.value).to_equal(3)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 119 |
| Active scenarios | 119 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
