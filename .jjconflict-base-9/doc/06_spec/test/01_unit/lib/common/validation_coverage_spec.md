# Validation & Result Helpers Coverage Specification

> Comprehensive branch-coverage tests for `src/lib/common/validation.spl` and `src/lib/common/result_helpers.spl`. Every exported function is exercised on both its true and false (or Ok/Err) branches, targeting 90%+ condition coverage.

<!-- sdn-diagram:id=validation_coverage_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=validation_coverage_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

validation_coverage_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=validation_coverage_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 182 | 182 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Validation & Result Helpers Coverage Specification

Comprehensive branch-coverage tests for `src/lib/common/validation.spl` and `src/lib/common/result_helpers.spl`. Every exported function is exercised on both its true and false (or Ok/Err) branches, targeting 90%+ condition coverage.

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #LIB-VALIDATION-COV |
| Category | Stdlib |
| Difficulty | 2/5 |
| Status | Implemented |
| Requirements | N/A |
| Plan | N/A |
| Design | N/A |
| Research | N/A |
| Source | `test/01_unit/lib/common/validation_coverage_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Comprehensive branch-coverage tests for `src/lib/common/validation.spl` and
`src/lib/common/result_helpers.spl`. Every exported function is exercised on
both its true and false (or Ok/Err) branches, targeting 90%+ condition coverage.

## Key Concepts

| Concept | Description |
|---------|-------------|
| Branch coverage | Each boolean branch taken at least once |
| Result pattern | Ok = [value, nil], Err = [nil, error] |

## Related Specifications

- [Result Spec](result_spec.spl) - Existing result tests
- [Option Spec](option_spec.spl) - Existing option tests

## Scenarios

### validation - is_valid_identifier

#### when valid

#### accepts lowercase letter start

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(is_valid_identifier("abc")).to_equal(true)
```

</details>

#### accepts underscore start

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(is_valid_identifier("_foo")).to_equal(true)
```

</details>

#### accepts uppercase start

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(is_valid_identifier("Abc")).to_equal(true)
```

</details>

#### accepts letters digits underscores

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(is_valid_identifier("my_var2")).to_equal(true)
```

</details>

#### accepts single letter

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(is_valid_identifier("x")).to_equal(true)
```

</details>

#### when invalid

#### rejects empty string

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(is_valid_identifier("")).to_equal(false)
```

</details>

#### rejects digit start

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(is_valid_identifier("1abc")).to_equal(false)
```

</details>

#### rejects hyphen in body

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(is_valid_identifier("a-b")).to_equal(false)
```

</details>

#### rejects space in body

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(is_valid_identifier("a b")).to_equal(false)
```

</details>

#### rejects special char start

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(is_valid_identifier("@foo")).to_equal(false)
```

</details>

### validation - is_numeric

#### when valid

#### accepts all digits

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(is_numeric("12345")).to_equal(true)
```

</details>

#### accepts single digit

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(is_numeric("0")).to_equal(true)
```

</details>

#### when invalid

#### rejects empty string

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(is_numeric("")).to_equal(false)
```

</details>

#### rejects letters

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(is_numeric("12a3")).to_equal(false)
```

</details>

#### rejects special chars

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(is_numeric("12.3")).to_equal(false)
```

</details>

### validation - is_alphanumeric

#### when valid

#### accepts letters and digits

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(is_alphanumeric("abc123")).to_equal(true)
```

</details>

#### accepts only letters

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(is_alphanumeric("abc")).to_equal(true)
```

</details>

#### accepts only digits

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(is_alphanumeric("123")).to_equal(true)
```

</details>

#### when invalid

#### rejects empty string

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(is_alphanumeric("")).to_equal(false)
```

</details>

#### rejects underscores

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(is_alphanumeric("abc_123")).to_equal(false)
```

</details>

#### rejects spaces

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(is_alphanumeric("abc 123")).to_equal(false)
```

</details>

### validation - is_hex_string

#### when valid

#### accepts lowercase hex

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(is_hex_string("0123456789abcdef")).to_equal(true)
```

</details>

#### accepts uppercase hex

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(is_hex_string("ABCDEF")).to_equal(true)
```

</details>

#### accepts mixed case hex

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(is_hex_string("aF09")).to_equal(true)
```

</details>

#### when invalid

#### rejects empty string

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(is_hex_string("")).to_equal(false)
```

</details>

#### rejects non-hex letter

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(is_hex_string("0g1")).to_equal(false)
```

</details>

#### rejects spaces

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(is_hex_string("ab cd")).to_equal(false)
```

</details>

### validation - is_email_like

#### when valid

#### accepts basic email

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(is_email_like("user@example.com")).to_equal(true)
```

</details>

#### accepts email with dot after at

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(is_email_like("a@b.c")).to_equal(true)
```

</details>

#### when invalid

#### rejects too short

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(is_email_like("ab")).to_equal(false)
```

</details>

#### rejects no at sign

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(is_email_like("userexample.com")).to_equal(false)
```

</details>

#### rejects at at start

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(is_email_like("@example.com")).to_equal(false)
```

</details>

#### rejects at at end

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(is_email_like("user@")).to_equal(false)
```

</details>

#### rejects multiple at signs

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(is_email_like("user@@example.com")).to_equal(false)
```

</details>

#### rejects no dot after at

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(is_email_like("user@examplecom")).to_equal(false)
```

</details>

#### rejects dot at very end only

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(is_email_like("user@example.")).to_equal(false)
```

</details>

### validation - is_positive_i64

#### returns true for positive

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(is_positive_i64(5)).to_equal(true)
```

</details>

#### returns false for zero

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(is_positive_i64(0)).to_equal(false)
```

</details>

#### returns false for negative

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(is_positive_i64(-3)).to_equal(false)
```

</details>

### validation - is_positive_f64

#### returns true for positive float

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(is_positive_f64(0.5)).to_equal(true)
```

</details>

#### returns false for zero float

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(is_positive_f64(0.0)).to_equal(false)
```

</details>

#### returns false for negative float

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(is_positive_f64(-1.5)).to_equal(false)
```

</details>

### validation - is_non_negative_i64

#### returns true for positive

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(is_non_negative_i64(1)).to_equal(true)
```

</details>

#### returns true for zero

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(is_non_negative_i64(0)).to_equal(true)
```

</details>

#### returns false for negative

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(is_non_negative_i64(-1)).to_equal(false)
```

</details>

### validation - is_non_negative_f64

#### returns true for positive float

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(is_non_negative_f64(0.1)).to_equal(true)
```

</details>

#### returns true for zero float

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(is_non_negative_f64(0.0)).to_equal(true)
```

</details>

#### returns false for negative float

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(is_non_negative_f64(-0.1)).to_equal(false)
```

</details>

### validation - is_positive alias

#### returns true for positive

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(is_positive(10)).to_equal(true)
```

</details>

#### returns false for zero

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(is_positive(0)).to_equal(false)
```

</details>

#### returns false for negative

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(is_positive(-10)).to_equal(false)
```

</details>

### validation - is_negative

#### returns true for negative

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(is_negative(-5)).to_equal(true)
```

</details>

#### returns false for zero

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(is_negative(0)).to_equal(false)
```

</details>

#### returns false for positive

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(is_negative(5)).to_equal(false)
```

</details>

### validation - is_non_negative alias

#### returns true for zero

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(is_non_negative(0)).to_equal(true)
```

</details>

#### returns true for positive

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(is_non_negative(5)).to_equal(true)
```

</details>

#### returns false for negative

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(is_non_negative(-5)).to_equal(false)
```

</details>

### validation - is_zero

#### returns true for zero

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(is_zero(0)).to_equal(true)
```

</details>

#### returns false for positive

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(is_zero(5)).to_equal(false)
```

</details>

#### returns false for negative

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(is_zero(-5)).to_equal(false)
```

</details>

### validation - clamp_i64

#### returns value when in range

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(clamp_i64(5, 0, 10)).to_equal(5)
```

</details>

#### clamps to min when below

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(clamp_i64(-5, 0, 10)).to_equal(0)
```

</details>

#### clamps to max when above

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(clamp_i64(15, 0, 10)).to_equal(10)
```

</details>

#### returns min when equal to min

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(clamp_i64(0, 0, 10)).to_equal(0)
```

</details>

#### returns max when equal to max

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(clamp_i64(10, 0, 10)).to_equal(10)
```

</details>

### validation - clamp alias

#### delegates to clamp_i64

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(clamp(5, 0, 10)).to_equal(5)
```

</details>

#### clamps below min

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(clamp(-1, 0, 10)).to_equal(0)
```

</details>

#### clamps above max

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(clamp(20, 0, 10)).to_equal(10)
```

</details>

### validation - clamp_f64

#### returns value when in range

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(clamp_f64(5.0, 0.0, 10.0)).to_equal(5.0)
```

</details>

#### clamps to min when below

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(clamp_f64(-1.0, 0.0, 10.0)).to_equal(0.0)
```

</details>

#### clamps to max when above

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(clamp_f64(15.0, 0.0, 10.0)).to_equal(10.0)
```

</details>

### validation - validate_length

#### returns true when length in range

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(validate_length("hello", 1, 10)).to_equal(true)
```

</details>

#### returns true at exact min

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(validate_length("hi", 2, 10)).to_equal(true)
```

</details>

#### returns true at exact max

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(validate_length("hi", 1, 2)).to_equal(true)
```

</details>

#### returns false when too short

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(validate_length("", 1, 10)).to_equal(false)
```

</details>

#### returns false when too long

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(validate_length("hello world", 1, 5)).to_equal(false)
```

</details>

### validation - validate_min_length

#### returns true when meets min

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(validate_min_length("hello", 3)).to_equal(true)
```

</details>

#### returns true at exact min

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(validate_min_length("hi", 2)).to_equal(true)
```

</details>

#### returns false when too short

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(validate_min_length("a", 5)).to_equal(false)
```

</details>

### validation - validate_max_length

#### returns true when within max

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(validate_max_length("hi", 5)).to_equal(true)
```

</details>

#### returns true at exact max

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(validate_max_length("hello", 5)).to_equal(true)
```

</details>

#### returns false when too long

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(validate_max_length("hello world", 5)).to_equal(false)
```

</details>

### validation - validate_array_length

#### returns true when in range

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(validate_array_length([1, 2, 3], 1, 5)).to_equal(true)
```

</details>

#### returns false when too short

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(validate_array_length([], 1, 5)).to_equal(false)
```

</details>

#### returns false when too long

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(validate_array_length([1, 2, 3, 4, 5, 6], 1, 5)).to_equal(false)
```

</details>

### validation - is_empty_array

#### returns true for empty array

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(is_empty_array([])).to_equal(true)
```

</details>

#### returns false for non-empty array

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(is_empty_array([1])).to_equal(false)
```

</details>

### validation - is_non_empty_array

#### returns true for non-empty array

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(is_non_empty_array([1, 2])).to_equal(true)
```

</details>

#### returns false for empty array

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(is_non_empty_array([])).to_equal(false)
```

</details>

### validation - is_empty

#### returns true for empty string

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(is_empty("")).to_equal(true)
```

</details>

#### returns false for non-empty string

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(is_empty("hello")).to_equal(false)
```

</details>

### validation - is_not_empty

#### returns true for non-empty string

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(is_not_empty("hello")).to_equal(true)
```

</details>

#### returns false for empty string

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(is_not_empty("")).to_equal(false)
```

</details>

### validation - is_in_range

#### returns true when in range

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(is_in_range(5, 0, 10)).to_equal(true)
```

</details>

#### returns true at min boundary

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(is_in_range(0, 0, 10)).to_equal(true)
```

</details>

#### returns true at max boundary

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(is_in_range(10, 0, 10)).to_equal(true)
```

</details>

#### returns false below range

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(is_in_range(-1, 0, 10)).to_equal(false)
```

</details>

#### returns false above range

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(is_in_range(11, 0, 10)).to_equal(false)
```

</details>

### validation - is_outside_range

#### returns true below range

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(is_outside_range(-1, 0, 10)).to_equal(true)
```

</details>

#### returns true above range

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(is_outside_range(11, 0, 10)).to_equal(true)
```

</details>

#### returns false when in range

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(is_outside_range(5, 0, 10)).to_equal(false)
```

</details>

#### returns false at min boundary

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(is_outside_range(0, 0, 10)).to_equal(false)
```

</details>

### validation - is_divisible

#### returns true when evenly divisible

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(is_divisible(10, 2)).to_equal(true)
```

</details>

#### returns false when not divisible

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(is_divisible(10, 3)).to_equal(false)
```

</details>

#### returns false when divisor is zero

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(is_divisible(10, 0)).to_equal(false)
```

</details>

#### returns true for zero dividend

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(is_divisible(0, 5)).to_equal(true)
```

</details>

### validation - is_multiple_of

#### returns true for multiple

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(is_multiple_of(15, 3)).to_equal(true)
```

</details>

#### returns false for non-multiple

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(is_multiple_of(15, 4)).to_equal(false)
```

</details>

#### returns false for zero factor

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(is_multiple_of(15, 0)).to_equal(false)
```

</details>

### validation - contains_only_letters

#### returns true for all letters

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(contains_only_letters("abcXYZ")).to_equal(true)
```

</details>

#### returns false for empty string

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(contains_only_letters("")).to_equal(false)
```

</details>

#### returns false when has digits

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(contains_only_letters("abc123")).to_equal(false)
```

</details>

#### returns false when has underscore

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(contains_only_letters("abc_def")).to_equal(false)
```

</details>

### validation - contains_only_digits

#### returns true for all digits

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(contains_only_digits("12345")).to_equal(true)
```

</details>

#### returns false for empty

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(contains_only_digits("")).to_equal(false)
```

</details>

#### returns false when has letters

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(contains_only_digits("12a")).to_equal(false)
```

</details>

### validation - contains_whitespace

#### returns true for space

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(contains_whitespace("hello world")).to_equal(true)
```

</details>

#### returns true for tab

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(contains_whitespace("hello\tworld")).to_equal(true)
```

</details>

#### returns false for no whitespace

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(contains_whitespace("helloworld")).to_equal(false)
```

</details>

#### returns false for empty string

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(contains_whitespace("")).to_equal(false)
```

</details>

### validation - starts_with_letter

#### returns true for lowercase start

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(starts_with_letter("abc")).to_equal(true)
```

</details>

#### returns true for uppercase start

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(starts_with_letter("Abc")).to_equal(true)
```

</details>

#### returns false for digit start

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(starts_with_letter("1abc")).to_equal(false)
```

</details>

#### returns false for empty string

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(starts_with_letter("")).to_equal(false)
```

</details>

#### returns false for underscore start

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(starts_with_letter("_abc")).to_equal(false)
```

</details>

### validation - is_valid_version

#### returns true for semver

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(is_valid_version("1.2.3")).to_equal(true)
```

</details>

#### returns true for two-part version

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(is_valid_version("1.0")).to_equal(true)
```

</details>

#### returns false for empty

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(is_valid_version("")).to_equal(false)
```

</details>

#### returns false for no dot

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(is_valid_version("123")).to_equal(false)
```

</details>

#### returns false for only dots

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(is_valid_version("...")).to_equal(false)
```

</details>

#### returns false for letters

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(is_valid_version("1.2.a")).to_equal(false)
```

</details>

### validation - is_valid_path_component

#### returns true for valid name

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(is_valid_path_component("myfile")).to_equal(true)
```

</details>

#### returns false for empty

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(is_valid_path_component("")).to_equal(false)
```

</details>

#### returns false for dot start

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(is_valid_path_component(".hidden")).to_equal(false)
```

</details>

#### returns false for forward slash

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(is_valid_path_component("path/to")).to_equal(false)
```

</details>

#### returns false for backslash

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(is_valid_path_component("path\\to")).to_equal(false)
```

</details>

### validation - require

#### returns nil when condition is true

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = require(true, "error msg")
expect(result == nil).to_equal(true)
```

</details>

#### returns Some message when condition is false

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = require(false, "must be valid")
expect(result.unwrap()).to_equal("must be valid")
```

</details>

### validation - require_all

#### returns empty array when all conditions pass

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val errors = require_all([(true, "err1"), (true, "err2")])
expect(errors.len()).to_equal(0)
```

</details>

#### collects messages for failed conditions

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val errors = require_all([(false, "err1"), (true, "ok"), (false, "err3")])
expect(errors.len()).to_equal(2)
expect(errors[0]).to_equal("err1")
expect(errors[1]).to_equal("err3")
```

</details>

#### returns all messages when all fail

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val errors = require_all([(false, "a"), (false, "b")])
expect(errors.len()).to_equal(2)
```

</details>

### Result enum - Ok and Err

#### Ok creates result with value

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val r = Ok(42)
expect(r.is_ok()).to_equal(true)
expect(r.unwrap()).to_equal(42)
```

</details>

#### Err creates result with error

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val r = Err("bad")
expect(r.is_err()).to_equal(true)
expect(r.unwrap_err()).to_equal("bad")
```

</details>

### Result enum - is_ok

#### returns true for Ok

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(Ok(42).is_ok()).to_equal(true)
```

</details>

#### returns false for Err

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(Err("e").is_ok()).to_equal(false)
```

</details>

### Result enum - is_err

#### returns true for Err

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(Err("e").is_err()).to_equal(true)
```

</details>

#### returns false for Ok

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(Ok(42).is_err()).to_equal(false)
```

</details>

### Result enum - unwrap_or

#### returns Ok value when Ok

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(Ok(42).unwrap_or(0)).to_equal(42)
```

</details>

#### returns default when Err

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(Err("e").unwrap_or(0)).to_equal(0)
```

</details>

### Result enum - unwrap

#### returns Ok value

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(Ok(42).unwrap()).to_equal(42)
```

</details>

### Result enum - unwrap_err

#### returns Err value

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(Err("bad").unwrap_err()).to_equal("bad")
```

</details>

### Result enum - unwrap_or_else

#### returns Ok value when Ok

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(Ok(42).unwrap_or_else(\_: 0)).to_equal(42)
```

</details>

#### calls function when Err

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(Err("e").unwrap_or_else(\_: 99)).to_equal(99)
```

</details>

### Result enum - map

#### maps Ok value

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val r = Ok(5).map(_1 * 2)
expect(r.is_ok()).to_equal(true)
expect(r.unwrap()).to_equal(10)
```

</details>

#### passes through Err

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val r = Err("e").map(_1 * 2)
expect(r.is_err()).to_equal(true)
expect(r.unwrap_err()).to_equal("e")
```

</details>

### Result enum - map_err

#### maps Err value

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val r = Err("io").map_err("Error: " + _1)
expect(r.is_err()).to_equal(true)
expect(r.unwrap_err()).to_equal("Error: io")
```

</details>

#### passes through Ok

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val r = Ok(5).map_err("Error: " + _1)
expect(r.is_ok()).to_equal(true)
expect(r.unwrap()).to_equal(5)
```

</details>

### Result enum - map then flatten

#### flat maps Ok value via map+flatten

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val mapped = Ok(5).map(Ok(_1 * 2))
val r = mapped.flatten()
expect(r.unwrap()).to_equal(10)
```

</details>

#### flat maps Ok to Err via map+flatten

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val mapped = Ok(5).map(\_: Err("bad"))
val r = mapped.flatten()
expect(r.is_err()).to_equal(true)
```

</details>

#### passes through Err with map

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val r = Err("e").map(Ok(_1 * 2))
expect(r.is_err()).to_equal(true)
```

</details>

### Result enum - or

#### returns first when first is Ok

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val r = Ok(5).or(Ok(10))
expect(r.unwrap()).to_equal(5)
```

</details>

#### returns second when first is Err

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val r = Err("e").or(Ok(10))
expect(r.unwrap()).to_equal(10)
```

</details>

#### returns second Err when both Err

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val r = Err("e1").or(Err("e2"))
expect(r.unwrap_err()).to_equal("e2")
```

</details>

### Result enum - or_else

#### returns Ok when Ok

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val r = Ok(5).or_else(\_: Ok(0))
expect(r.unwrap()).to_equal(5)
```

</details>

#### calls function when Err

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val r = Err("e").or_else(\_: Ok(99))
expect(r.unwrap()).to_equal(99)
```

</details>

### Result enum - flatten

#### flattens Ok(Ok(v)) to Ok(v)

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val r = Ok(Ok(5)).flatten()
expect(r.unwrap()).to_equal(5)
```

</details>

#### flattens Ok(Err(e)) to Err(e)

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val r = Ok(Err("e")).flatten()
expect(r.is_err()).to_equal(true)
```

</details>

#### passes through outer Err

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val r = Err("outer").flatten()
expect(r.is_err()).to_equal(true)
```

</details>

### Result enum - unwrap_or with Err

#### returns default for Err via unwrap_or

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val r = Err("e")
expect(r.unwrap_or(99)).to_equal(99)
```

</details>

#### returns value for Ok via unwrap_or

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val r = Ok(5)
expect(r.unwrap_or(99)).to_equal(5)
```

</details>

### Result enum - ok

#### returns Some(value) for Ok

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val opt = Ok(42).ok()
expect(opt.unwrap()).to_equal(42)
```

</details>

#### returns None for Err

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val opt = Err("e").ok()
expect(opt.?).to_equal(false)
```

</details>

### Result enum - err

#### returns Some(error) for Err

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val opt = Err("bad").err()
expect(opt.unwrap()).to_equal("bad")
```

</details>

#### returns None for Ok

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val opt = Ok(42).err()
expect(opt.?).to_equal(false)
```

</details>

### Result enum - expect

#### returns Ok value with expect

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(Ok(42).expect("should be ok")).to_equal(42)
```

</details>

### Result enum - expect_err

#### returns Err value with expect_err

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(Err("bad").expect_err("should be err")).to_equal("bad")
```

</details>

### Result enum - map_err chaining

#### maps error and checks original Ok preserved

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val r = Ok(10).map_err("wrapped: " + _1)
expect(r.is_ok()).to_equal(true)
expect(r.unwrap()).to_equal(10)
```

</details>

#### maps error message on Err

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val r = Err("timeout").map_err("wrapped: " + _1)
expect(r.is_err()).to_equal(true)
expect(r.unwrap_err()).to_equal("wrapped: timeout")
```

</details>

### Result enum - or_else chaining

#### returns recovery value on Err

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val r = Err("first").or_else(\_: Err("fallback"))
expect(r.is_err()).to_equal(true)
expect(r.unwrap_err()).to_equal("fallback")
```

</details>

#### ignores or_else on Ok

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val r = Ok(42).or_else(\_: Ok(0))
expect(r.unwrap()).to_equal(42)
```

</details>

### Result enum - flatten nested

#### flattens nested Ok

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val r = Ok(Ok(100)).flatten()
expect(r.unwrap()).to_equal(100)
```

</details>

#### flattens nested Err inside Ok

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val r = Ok(Err("inner")).flatten()
expect(r.is_err()).to_equal(true)
expect(r.unwrap_err()).to_equal("inner")
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 182 |
| Active scenarios | 182 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
