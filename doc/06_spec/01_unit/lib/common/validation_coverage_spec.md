# Validation & Result Helpers Coverage Specification

> Purpose: Prove that validation - is_valid_identifier.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 182 | 182 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Validation & Result Helpers Coverage Specification

Purpose: Prove that validation - is_valid_identifier.

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
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Purpose and audience
Purpose: Prove that validation - is_valid_identifier.
Audience: compiler and tooling engineers who maintain this spec.

## Scenarios

### validation - is_valid_identifier

#### when valid

#### accepts lowercase letter start

- accepts lowercase letter start
- Verify: accepts lowercase letter start
   - Expected: is_valid_identifier("abc") is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("accepts lowercase letter start")
step("Verify: accepts lowercase letter start")
# @req: REQ-LIB-COMMON-001
expect(is_valid_identifier("abc")).to_equal(true)
```

</details>

#### accepts underscore start

- accepts underscore start
- Verify: accepts underscore start
   - Expected: is_valid_identifier("_foo") is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("accepts underscore start")
step("Verify: accepts underscore start")
expect(is_valid_identifier("_foo")).to_equal(true)
```

</details>

#### accepts uppercase start

- accepts uppercase start
- Verify: accepts uppercase start
   - Expected: is_valid_identifier("Abc") is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("accepts uppercase start")
step("Verify: accepts uppercase start")
expect(is_valid_identifier("Abc")).to_equal(true)
```

</details>

#### accepts letters digits underscores

- accepts letters digits underscores
- Verify: accepts letters digits underscores
   - Expected: is_valid_identifier("my_var2") is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("accepts letters digits underscores")
step("Verify: accepts letters digits underscores")
expect(is_valid_identifier("my_var2")).to_equal(true)
```

</details>

#### accepts single letter

- accepts single letter
- Verify: accepts single letter
   - Expected: is_valid_identifier("x") is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("accepts single letter")
step("Verify: accepts single letter")
expect(is_valid_identifier("x")).to_equal(true)
```

</details>

#### when invalid

#### rejects empty string

- rejects empty string
- Verify: rejects empty string
   - Expected: is_valid_identifier("") is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("rejects empty string")
step("Verify: rejects empty string")
expect(is_valid_identifier("")).to_equal(false)
```

</details>

#### rejects digit start

- rejects digit start
- Verify: rejects digit start
   - Expected: is_valid_identifier("1abc") is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("rejects digit start")
step("Verify: rejects digit start")
expect(is_valid_identifier("1abc")).to_equal(false)
```

</details>

#### rejects hyphen in body

- rejects hyphen in body
- Verify: rejects hyphen in body
   - Expected: is_valid_identifier("a-b") is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("rejects hyphen in body")
step("Verify: rejects hyphen in body")
expect(is_valid_identifier("a-b")).to_equal(false)
```

</details>

#### rejects space in body

- rejects space in body
- Verify: rejects space in body
   - Expected: is_valid_identifier("a b") is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("rejects space in body")
step("Verify: rejects space in body")
expect(is_valid_identifier("a b")).to_equal(false)
```

</details>

#### rejects special char start

- rejects special char start
- Verify: rejects special char start
   - Expected: is_valid_identifier("@foo") is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("rejects special char start")
step("Verify: rejects special char start")
expect(is_valid_identifier("@foo")).to_equal(false)
```

</details>

### validation - is_numeric

#### when valid

#### accepts all digits

- accepts all digits
- Verify: accepts all digits
   - Expected: is_numeric("12345") is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("accepts all digits")
step("Verify: accepts all digits")
expect(is_numeric("12345")).to_equal(true)
```

</details>

#### accepts single digit

- accepts single digit
- Verify: accepts single digit
   - Expected: is_numeric("0") is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("accepts single digit")
step("Verify: accepts single digit")
expect(is_numeric("0")).to_equal(true)
```

</details>

#### when invalid

#### rejects empty string

- rejects empty string
- Verify: rejects empty string
   - Expected: is_numeric("") is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("rejects empty string")
step("Verify: rejects empty string")
expect(is_numeric("")).to_equal(false)
```

</details>

#### rejects letters

- rejects letters
- Verify: rejects letters
   - Expected: is_numeric("12a3") is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("rejects letters")
step("Verify: rejects letters")
expect(is_numeric("12a3")).to_equal(false)
```

</details>

#### rejects special chars

- rejects special chars
- Verify: rejects special chars
   - Expected: is_numeric("12.3") is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("rejects special chars")
step("Verify: rejects special chars")
expect(is_numeric("12.3")).to_equal(false)
```

</details>

### validation - is_alphanumeric

#### when valid

#### accepts letters and digits

- accepts letters and digits
- Verify: accepts letters and digits
   - Expected: is_alphanumeric("abc123") is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("accepts letters and digits")
step("Verify: accepts letters and digits")
expect(is_alphanumeric("abc123")).to_equal(true)
```

</details>

#### accepts only letters

- accepts only letters
- Verify: accepts only letters
   - Expected: is_alphanumeric("abc") is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("accepts only letters")
step("Verify: accepts only letters")
expect(is_alphanumeric("abc")).to_equal(true)
```

</details>

#### accepts only digits

- accepts only digits
- Verify: accepts only digits
   - Expected: is_alphanumeric("123") is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("accepts only digits")
step("Verify: accepts only digits")
expect(is_alphanumeric("123")).to_equal(true)
```

</details>

#### when invalid

#### rejects empty string

- rejects empty string
- Verify: rejects empty string
   - Expected: is_alphanumeric("") is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("rejects empty string")
step("Verify: rejects empty string")
expect(is_alphanumeric("")).to_equal(false)
```

</details>

#### rejects underscores

- rejects underscores
- Verify: rejects underscores
   - Expected: is_alphanumeric("abc_123") is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("rejects underscores")
step("Verify: rejects underscores")
expect(is_alphanumeric("abc_123")).to_equal(false)
```

</details>

#### rejects spaces

- rejects spaces
- Verify: rejects spaces
   - Expected: is_alphanumeric("abc 123") is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("rejects spaces")
step("Verify: rejects spaces")
expect(is_alphanumeric("abc 123")).to_equal(false)
```

</details>

### validation - is_hex_string

#### when valid

#### accepts lowercase hex

- accepts lowercase hex
- Verify: accepts lowercase hex
   - Expected: is_hex_string("0123456789abcdef") is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("accepts lowercase hex")
step("Verify: accepts lowercase hex")
expect(is_hex_string("0123456789abcdef")).to_equal(true)
```

</details>

#### accepts uppercase hex

- accepts uppercase hex
- Verify: accepts uppercase hex
   - Expected: is_hex_string("ABCDEF") is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("accepts uppercase hex")
step("Verify: accepts uppercase hex")
expect(is_hex_string("ABCDEF")).to_equal(true)
```

</details>

#### accepts mixed case hex

- accepts mixed case hex
- Verify: accepts mixed case hex
   - Expected: is_hex_string("aF09") is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("accepts mixed case hex")
step("Verify: accepts mixed case hex")
expect(is_hex_string("aF09")).to_equal(true)
```

</details>

#### when invalid

#### rejects empty string

- rejects empty string
- Verify: rejects empty string
   - Expected: is_hex_string("") is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("rejects empty string")
step("Verify: rejects empty string")
expect(is_hex_string("")).to_equal(false)
```

</details>

#### rejects non-hex letter

- rejects non-hex letter
- Verify: rejects non-hex letter
   - Expected: is_hex_string("0g1") is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("rejects non-hex letter")
step("Verify: rejects non-hex letter")
expect(is_hex_string("0g1")).to_equal(false)
```

</details>

#### rejects spaces

- rejects spaces
- Verify: rejects spaces
   - Expected: is_hex_string("ab cd") is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("rejects spaces")
step("Verify: rejects spaces")
expect(is_hex_string("ab cd")).to_equal(false)
```

</details>

### validation - is_email_like

#### when valid

#### accepts basic email

- accepts basic email
- Verify: accepts basic email
   - Expected: is_email_like("user@example.com") is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("accepts basic email")
step("Verify: accepts basic email")
expect(is_email_like("user@example.com")).to_equal(true)
```

</details>

#### accepts email with dot after at

- accepts email with dot after at
- Verify: accepts email with dot after at
   - Expected: is_email_like("a@b.c") is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("accepts email with dot after at")
step("Verify: accepts email with dot after at")
expect(is_email_like("a@b.c")).to_equal(true)
```

</details>

#### when invalid

#### rejects too short

- rejects too short
- Verify: rejects too short
   - Expected: is_email_like("ab") is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("rejects too short")
step("Verify: rejects too short")
expect(is_email_like("ab")).to_equal(false)
```

</details>

#### rejects no at sign

- rejects no at sign
- Verify: rejects no at sign
   - Expected: is_email_like("userexample.com") is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("rejects no at sign")
step("Verify: rejects no at sign")
expect(is_email_like("userexample.com")).to_equal(false)
```

</details>

#### rejects at at start

- rejects at at start
- Verify: rejects at at start
   - Expected: is_email_like("@example.com") is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("rejects at at start")
step("Verify: rejects at at start")
expect(is_email_like("@example.com")).to_equal(false)
```

</details>

#### rejects at at end

- rejects at at end
- Verify: rejects at at end
   - Expected: is_email_like("user@") is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("rejects at at end")
step("Verify: rejects at at end")
expect(is_email_like("user@")).to_equal(false)
```

</details>

#### rejects multiple at signs

- rejects multiple at signs
- Verify: rejects multiple at signs
   - Expected: is_email_like("user@@example.com") is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("rejects multiple at signs")
step("Verify: rejects multiple at signs")
expect(is_email_like("user@@example.com")).to_equal(false)
```

</details>

#### rejects no dot after at

- rejects no dot after at
- Verify: rejects no dot after at
   - Expected: is_email_like("user@examplecom") is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("rejects no dot after at")
step("Verify: rejects no dot after at")
expect(is_email_like("user@examplecom")).to_equal(false)
```

</details>

#### rejects dot at very end only

- rejects dot at very end only
- Verify: rejects dot at very end only
   - Expected: is_email_like("user@example.") is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("rejects dot at very end only")
step("Verify: rejects dot at very end only")
expect(is_email_like("user@example.")).to_equal(false)
```

</details>

### validation - is_positive_i64

#### returns true for positive

- returns true for positive
- Verify: returns true for positive
   - Expected: is_positive_i64(5) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("returns true for positive")
step("Verify: returns true for positive")
expect(is_positive_i64(5)).to_equal(true)
```

</details>

#### returns false for zero

- returns false for zero
- Verify: returns false for zero
   - Expected: is_positive_i64(0) is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("returns false for zero")
step("Verify: returns false for zero")
expect(is_positive_i64(0)).to_equal(false)
```

</details>

#### returns false for negative

- returns false for negative
- Verify: returns false for negative
   - Expected: is_positive_i64(-3) is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("returns false for negative")
step("Verify: returns false for negative")
expect(is_positive_i64(-3)).to_equal(false)
```

</details>

### validation - is_positive_f64

#### returns true for positive float

- returns true for positive float
- Verify: returns true for positive float
   - Expected: is_positive_f64(0.5) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("returns true for positive float")
step("Verify: returns true for positive float")
expect(is_positive_f64(0.5)).to_equal(true)
```

</details>

#### returns false for zero float

- returns false for zero float
- Verify: returns false for zero float
   - Expected: is_positive_f64(0.0) is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("returns false for zero float")
step("Verify: returns false for zero float")
expect(is_positive_f64(0.0)).to_equal(false)
```

</details>

#### returns false for negative float

- returns false for negative float
- Verify: returns false for negative float
   - Expected: is_positive_f64(-1.5) is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("returns false for negative float")
step("Verify: returns false for negative float")
expect(is_positive_f64(-1.5)).to_equal(false)
```

</details>

### validation - is_non_negative_i64

#### returns true for positive

- returns true for positive
- Verify: returns true for positive
   - Expected: is_non_negative_i64(1) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("returns true for positive")
step("Verify: returns true for positive")
expect(is_non_negative_i64(1)).to_equal(true)
```

</details>

#### returns true for zero

- returns true for zero
- Verify: returns true for zero
   - Expected: is_non_negative_i64(0) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("returns true for zero")
step("Verify: returns true for zero")
expect(is_non_negative_i64(0)).to_equal(true)
```

</details>

#### returns false for negative

- returns false for negative
- Verify: returns false for negative
   - Expected: is_non_negative_i64(-1) is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("returns false for negative")
step("Verify: returns false for negative")
expect(is_non_negative_i64(-1)).to_equal(false)
```

</details>

### validation - is_non_negative_f64

#### returns true for positive float

- returns true for positive float
- Verify: returns true for positive float
   - Expected: is_non_negative_f64(0.1) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("returns true for positive float")
step("Verify: returns true for positive float")
expect(is_non_negative_f64(0.1)).to_equal(true)
```

</details>

#### returns true for zero float

- returns true for zero float
- Verify: returns true for zero float
   - Expected: is_non_negative_f64(0.0) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("returns true for zero float")
step("Verify: returns true for zero float")
expect(is_non_negative_f64(0.0)).to_equal(true)
```

</details>

#### returns false for negative float

- returns false for negative float
- Verify: returns false for negative float
   - Expected: is_non_negative_f64(-0.1) is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("returns false for negative float")
step("Verify: returns false for negative float")
expect(is_non_negative_f64(-0.1)).to_equal(false)
```

</details>

### validation - is_positive alias

#### returns true for positive

- returns true for positive
- Verify: returns true for positive
   - Expected: is_positive(10) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("returns true for positive")
step("Verify: returns true for positive")
expect(is_positive(10)).to_equal(true)
```

</details>

#### returns false for zero

- returns false for zero
- Verify: returns false for zero
   - Expected: is_positive(0) is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("returns false for zero")
step("Verify: returns false for zero")
expect(is_positive(0)).to_equal(false)
```

</details>

#### returns false for negative

- returns false for negative
- Verify: returns false for negative
   - Expected: is_positive(-10) is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("returns false for negative")
step("Verify: returns false for negative")
expect(is_positive(-10)).to_equal(false)
```

</details>

### validation - is_negative

#### returns true for negative

- returns true for negative
- Verify: returns true for negative
   - Expected: is_negative(-5) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("returns true for negative")
step("Verify: returns true for negative")
expect(is_negative(-5)).to_equal(true)
```

</details>

#### returns false for zero

- returns false for zero
- Verify: returns false for zero
   - Expected: is_negative(0) is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("returns false for zero")
step("Verify: returns false for zero")
expect(is_negative(0)).to_equal(false)
```

</details>

#### returns false for positive

- returns false for positive
- Verify: returns false for positive
   - Expected: is_negative(5) is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("returns false for positive")
step("Verify: returns false for positive")
expect(is_negative(5)).to_equal(false)
```

</details>

### validation - is_non_negative alias

#### returns true for zero

- returns true for zero
- Verify: returns true for zero
   - Expected: is_non_negative(0) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("returns true for zero")
step("Verify: returns true for zero")
expect(is_non_negative(0)).to_equal(true)
```

</details>

#### returns true for positive

- returns true for positive
- Verify: returns true for positive
   - Expected: is_non_negative(5) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("returns true for positive")
step("Verify: returns true for positive")
expect(is_non_negative(5)).to_equal(true)
```

</details>

#### returns false for negative

- returns false for negative
- Verify: returns false for negative
   - Expected: is_non_negative(-5) is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("returns false for negative")
step("Verify: returns false for negative")
expect(is_non_negative(-5)).to_equal(false)
```

</details>

### validation - is_zero

#### returns true for zero

- returns true for zero
- Verify: returns true for zero
   - Expected: is_zero(0) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("returns true for zero")
step("Verify: returns true for zero")
expect(is_zero(0)).to_equal(true)
```

</details>

#### returns false for positive

- returns false for positive
- Verify: returns false for positive
   - Expected: is_zero(5) is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("returns false for positive")
step("Verify: returns false for positive")
expect(is_zero(5)).to_equal(false)
```

</details>

#### returns false for negative

- returns false for negative
- Verify: returns false for negative
   - Expected: is_zero(-5) is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("returns false for negative")
step("Verify: returns false for negative")
expect(is_zero(-5)).to_equal(false)
```

</details>

### validation - clamp_i64

#### returns value when in range

- returns value when in range
- Verify: returns value when in range
   - Expected: clamp_i64(5, 0, 10) equals `5`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("returns value when in range")
step("Verify: returns value when in range")
expect(clamp_i64(5, 0, 10)).to_equal(5)  # oracle: 5 — named expected value from the requirement
```

</details>

#### clamps to min when below

- clamps to min when below
- Verify: clamps to min when below
   - Expected: clamp_i64(-5, 0, 10) equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("clamps to min when below")
step("Verify: clamps to min when below")
expect(clamp_i64(-5, 0, 10)).to_equal(0)  # oracle: 0 — named expected value from the requirement
```

</details>

#### clamps to max when above

- clamps to max when above
- Verify: clamps to max when above
   - Expected: clamp_i64(15, 0, 10) equals `10`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("clamps to max when above")
step("Verify: clamps to max when above")
expect(clamp_i64(15, 0, 10)).to_equal(10)  # oracle: 10 — named expected value from the requirement
```

</details>

#### returns min when equal to min

- returns min when equal to min
- Verify: returns min when equal to min
   - Expected: clamp_i64(0, 0, 10) equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("returns min when equal to min")
step("Verify: returns min when equal to min")
expect(clamp_i64(0, 0, 10)).to_equal(0)  # oracle: 0 — named expected value from the requirement
```

</details>

#### returns max when equal to max

- returns max when equal to max
- Verify: returns max when equal to max
   - Expected: clamp_i64(10, 0, 10) equals `10`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("returns max when equal to max")
step("Verify: returns max when equal to max")
expect(clamp_i64(10, 0, 10)).to_equal(10)  # oracle: 10 — named expected value from the requirement
```

</details>

### validation - clamp alias

#### delegates to clamp_i64

- delegates to clamp_i64
- Verify: delegates to clamp_i64
   - Expected: clamp(5, 0, 10) equals `5`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("delegates to clamp_i64")
step("Verify: delegates to clamp_i64")
expect(clamp(5, 0, 10)).to_equal(5)  # oracle: 5 — named expected value from the requirement
```

</details>

#### clamps below min

- clamps below min
- Verify: clamps below min
   - Expected: clamp(-1, 0, 10) equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("clamps below min")
step("Verify: clamps below min")
expect(clamp(-1, 0, 10)).to_equal(0)  # oracle: 0 — named expected value from the requirement
```

</details>

#### clamps above max

- clamps above max
- Verify: clamps above max
   - Expected: clamp(20, 0, 10) equals `10`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("clamps above max")
step("Verify: clamps above max")
expect(clamp(20, 0, 10)).to_equal(10)  # oracle: 10 — named expected value from the requirement
```

</details>

### validation - clamp_f64

#### returns value when in range

- returns value when in range
- Verify: returns value when in range
   - Expected: clamp_f64(5.0, 0.0, 10.0) equals `5.0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("returns value when in range")
step("Verify: returns value when in range")
expect(clamp_f64(5.0, 0.0, 10.0)).to_equal(5.0)  # oracle: 5.0 — named expected value from the requirement
```

</details>

#### clamps to min when below

- clamps to min when below
- Verify: clamps to min when below
   - Expected: clamp_f64(-1.0, 0.0, 10.0) equals `0.0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("clamps to min when below")
step("Verify: clamps to min when below")
expect(clamp_f64(-1.0, 0.0, 10.0)).to_equal(0.0)  # oracle: 0.0 — named expected value from the requirement
```

</details>

#### clamps to max when above

- clamps to max when above
- Verify: clamps to max when above
   - Expected: clamp_f64(15.0, 0.0, 10.0) equals `10.0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("clamps to max when above")
step("Verify: clamps to max when above")
expect(clamp_f64(15.0, 0.0, 10.0)).to_equal(10.0)  # oracle: 10.0 — named expected value from the requirement
```

</details>

### validation - validate_length

#### returns true when length in range

- returns true when length in range
- Verify: returns true when length in range
   - Expected: validate_length("hello", 1, 10) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("returns true when length in range")
step("Verify: returns true when length in range")
expect(validate_length("hello", 1, 10)).to_equal(true)
```

</details>

#### returns true at exact min

- returns true at exact min
- Verify: returns true at exact min
   - Expected: validate_length("hi", 2, 10) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("returns true at exact min")
step("Verify: returns true at exact min")
expect(validate_length("hi", 2, 10)).to_equal(true)
```

</details>

#### returns true at exact max

- returns true at exact max
- Verify: returns true at exact max
   - Expected: validate_length("hi", 1, 2) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("returns true at exact max")
step("Verify: returns true at exact max")
expect(validate_length("hi", 1, 2)).to_equal(true)
```

</details>

#### returns false when too short

- returns false when too short
- Verify: returns false when too short
   - Expected: validate_length("", 1, 10) is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("returns false when too short")
step("Verify: returns false when too short")
expect(validate_length("", 1, 10)).to_equal(false)
```

</details>

#### returns false when too long

- returns false when too long
- Verify: returns false when too long
   - Expected: validate_length("hello world", 1, 5) is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("returns false when too long")
step("Verify: returns false when too long")
expect(validate_length("hello world", 1, 5)).to_equal(false)
```

</details>

### validation - validate_min_length

#### returns true when meets min

- returns true when meets min
- Verify: returns true when meets min
   - Expected: validate_min_length("hello", 3) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("returns true when meets min")
step("Verify: returns true when meets min")
expect(validate_min_length("hello", 3)).to_equal(true)
```

</details>

#### returns true at exact min

- returns true at exact min
- Verify: returns true at exact min
   - Expected: validate_min_length("hi", 2) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("returns true at exact min")
step("Verify: returns true at exact min")
expect(validate_min_length("hi", 2)).to_equal(true)
```

</details>

#### returns false when too short

- returns false when too short
- Verify: returns false when too short
   - Expected: validate_min_length("a", 5) is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("returns false when too short")
step("Verify: returns false when too short")
expect(validate_min_length("a", 5)).to_equal(false)
```

</details>

### validation - validate_max_length

#### returns true when within max

- returns true when within max
- Verify: returns true when within max
   - Expected: validate_max_length("hi", 5) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("returns true when within max")
step("Verify: returns true when within max")
expect(validate_max_length("hi", 5)).to_equal(true)
```

</details>

#### returns true at exact max

- returns true at exact max
- Verify: returns true at exact max
   - Expected: validate_max_length("hello", 5) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("returns true at exact max")
step("Verify: returns true at exact max")
expect(validate_max_length("hello", 5)).to_equal(true)
```

</details>

#### returns false when too long

- returns false when too long
- Verify: returns false when too long
   - Expected: validate_max_length("hello world", 5) is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("returns false when too long")
step("Verify: returns false when too long")
expect(validate_max_length("hello world", 5)).to_equal(false)
```

</details>

### validation - validate_array_length

#### returns true when in range

- returns true when in range
- Verify: returns true when in range
   - Expected: validate_array_length([1, 2, 3], 1, 5) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("returns true when in range")
step("Verify: returns true when in range")
expect(validate_array_length([1, 2, 3], 1, 5)).to_equal(true)
```

</details>

#### returns false when too short

- returns false when too short
- Verify: returns false when too short
   - Expected: validate_array_length([], 1, 5) is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("returns false when too short")
step("Verify: returns false when too short")
expect(validate_array_length([], 1, 5)).to_equal(false)
```

</details>

#### returns false when too long

- returns false when too long
- Verify: returns false when too long
   - Expected: validate_array_length([1, 2, 3, 4, 5, 6], 1, 5) is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("returns false when too long")
step("Verify: returns false when too long")
expect(validate_array_length([1, 2, 3, 4, 5, 6], 1, 5)).to_equal(false)
```

</details>

### validation - is_empty_array

#### returns true for empty array

- returns true for empty array
- Verify: returns true for empty array
   - Expected: is_empty_array([]) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("returns true for empty array")
step("Verify: returns true for empty array")
expect(is_empty_array([])).to_equal(true)
```

</details>

#### returns false for non-empty array

- returns false for non-empty array
- Verify: returns false for non-empty array
   - Expected: is_empty_array([1]) is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("returns false for non-empty array")
step("Verify: returns false for non-empty array")
expect(is_empty_array([1])).to_equal(false)
```

</details>

### validation - is_non_empty_array

#### returns true for non-empty array

- returns true for non-empty array
- Verify: returns true for non-empty array
   - Expected: is_non_empty_array([1, 2]) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("returns true for non-empty array")
step("Verify: returns true for non-empty array")
expect(is_non_empty_array([1, 2])).to_equal(true)
```

</details>

#### returns false for empty array

- returns false for empty array
- Verify: returns false for empty array
   - Expected: is_non_empty_array([]) is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("returns false for empty array")
step("Verify: returns false for empty array")
expect(is_non_empty_array([])).to_equal(false)
```

</details>

### validation - is_empty

#### returns true for empty string

- returns true for empty string
- Verify: returns true for empty string
   - Expected: is_empty("") is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("returns true for empty string")
step("Verify: returns true for empty string")
expect(is_empty("")).to_equal(true)
```

</details>

#### returns false for non-empty string

- returns false for non-empty string
- Verify: returns false for non-empty string
   - Expected: is_empty("hello") is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("returns false for non-empty string")
step("Verify: returns false for non-empty string")
expect(is_empty("hello")).to_equal(false)
```

</details>

### validation - is_not_empty

#### returns true for non-empty string

- returns true for non-empty string
- Verify: returns true for non-empty string
   - Expected: is_not_empty("hello") is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("returns true for non-empty string")
step("Verify: returns true for non-empty string")
expect(is_not_empty("hello")).to_equal(true)
```

</details>

#### returns false for empty string

- returns false for empty string
- Verify: returns false for empty string
   - Expected: is_not_empty("") is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("returns false for empty string")
step("Verify: returns false for empty string")
expect(is_not_empty("")).to_equal(false)
```

</details>

### validation - is_in_range

#### returns true when in range

- returns true when in range
- Verify: returns true when in range
   - Expected: is_in_range(5, 0, 10) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("returns true when in range")
step("Verify: returns true when in range")
expect(is_in_range(5, 0, 10)).to_equal(true)
```

</details>

#### returns true at min boundary

- returns true at min boundary
- Verify: returns true at min boundary
   - Expected: is_in_range(0, 0, 10) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("returns true at min boundary")
step("Verify: returns true at min boundary")
expect(is_in_range(0, 0, 10)).to_equal(true)
```

</details>

#### returns true at max boundary

- returns true at max boundary
- Verify: returns true at max boundary
   - Expected: is_in_range(10, 0, 10) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("returns true at max boundary")
step("Verify: returns true at max boundary")
expect(is_in_range(10, 0, 10)).to_equal(true)
```

</details>

#### returns false below range

- returns false below range
- Verify: returns false below range
   - Expected: is_in_range(-1, 0, 10) is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("returns false below range")
step("Verify: returns false below range")
expect(is_in_range(-1, 0, 10)).to_equal(false)
```

</details>

#### returns false above range

- returns false above range
- Verify: returns false above range
   - Expected: is_in_range(11, 0, 10) is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("returns false above range")
step("Verify: returns false above range")
expect(is_in_range(11, 0, 10)).to_equal(false)
```

</details>

### validation - is_outside_range

#### returns true below range

- returns true below range
- Verify: returns true below range
   - Expected: is_outside_range(-1, 0, 10) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("returns true below range")
step("Verify: returns true below range")
expect(is_outside_range(-1, 0, 10)).to_equal(true)
```

</details>

#### returns true above range

- returns true above range
- Verify: returns true above range
   - Expected: is_outside_range(11, 0, 10) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("returns true above range")
step("Verify: returns true above range")
expect(is_outside_range(11, 0, 10)).to_equal(true)
```

</details>

#### returns false when in range

- returns false when in range
- Verify: returns false when in range
   - Expected: is_outside_range(5, 0, 10) is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("returns false when in range")
step("Verify: returns false when in range")
expect(is_outside_range(5, 0, 10)).to_equal(false)
```

</details>

#### returns false at min boundary

- returns false at min boundary
- Verify: returns false at min boundary
   - Expected: is_outside_range(0, 0, 10) is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("returns false at min boundary")
step("Verify: returns false at min boundary")
expect(is_outside_range(0, 0, 10)).to_equal(false)
```

</details>

### validation - is_divisible

#### returns true when evenly divisible

- returns true when evenly divisible
- Verify: returns true when evenly divisible
   - Expected: is_divisible(10, 2) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("returns true when evenly divisible")
step("Verify: returns true when evenly divisible")
expect(is_divisible(10, 2)).to_equal(true)
```

</details>

#### returns false when not divisible

- returns false when not divisible
- Verify: returns false when not divisible
   - Expected: is_divisible(10, 3) is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("returns false when not divisible")
step("Verify: returns false when not divisible")
expect(is_divisible(10, 3)).to_equal(false)
```

</details>

#### returns false when divisor is zero

- returns false when divisor is zero
- Verify: returns false when divisor is zero
   - Expected: is_divisible(10, 0) is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("returns false when divisor is zero")
step("Verify: returns false when divisor is zero")
expect(is_divisible(10, 0)).to_equal(false)
```

</details>

#### returns true for zero dividend

- returns true for zero dividend
- Verify: returns true for zero dividend
   - Expected: is_divisible(0, 5) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("returns true for zero dividend")
step("Verify: returns true for zero dividend")
expect(is_divisible(0, 5)).to_equal(true)
```

</details>

### validation - is_multiple_of

#### returns true for multiple

- returns true for multiple
- Verify: returns true for multiple
   - Expected: is_multiple_of(15, 3) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("returns true for multiple")
step("Verify: returns true for multiple")
expect(is_multiple_of(15, 3)).to_equal(true)
```

</details>

#### returns false for non-multiple

- returns false for non-multiple
- Verify: returns false for non-multiple
   - Expected: is_multiple_of(15, 4) is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("returns false for non-multiple")
step("Verify: returns false for non-multiple")
expect(is_multiple_of(15, 4)).to_equal(false)
```

</details>

#### returns false for zero factor

- returns false for zero factor
- Verify: returns false for zero factor
   - Expected: is_multiple_of(15, 0) is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("returns false for zero factor")
step("Verify: returns false for zero factor")
expect(is_multiple_of(15, 0)).to_equal(false)
```

</details>

### validation - contains_only_letters

#### returns true for all letters

- returns true for all letters
- Verify: returns true for all letters
   - Expected: contains_only_letters("abcXYZ") is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("returns true for all letters")
step("Verify: returns true for all letters")
expect(contains_only_letters("abcXYZ")).to_equal(true)
```

</details>

#### returns false for empty string

- returns false for empty string
- Verify: returns false for empty string
   - Expected: contains_only_letters("") is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("returns false for empty string")
step("Verify: returns false for empty string")
expect(contains_only_letters("")).to_equal(false)
```

</details>

#### returns false when has digits

- returns false when has digits
- Verify: returns false when has digits
   - Expected: contains_only_letters("abc123") is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("returns false when has digits")
step("Verify: returns false when has digits")
expect(contains_only_letters("abc123")).to_equal(false)
```

</details>

#### returns false when has underscore

- returns false when has underscore
- Verify: returns false when has underscore
   - Expected: contains_only_letters("abc_def") is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("returns false when has underscore")
step("Verify: returns false when has underscore")
expect(contains_only_letters("abc_def")).to_equal(false)
```

</details>

### validation - contains_only_digits

#### returns true for all digits

- returns true for all digits
- Verify: returns true for all digits
   - Expected: contains_only_digits("12345") is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("returns true for all digits")
step("Verify: returns true for all digits")
expect(contains_only_digits("12345")).to_equal(true)
```

</details>

#### returns false for empty

- returns false for empty
- Verify: returns false for empty
   - Expected: contains_only_digits("") is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("returns false for empty")
step("Verify: returns false for empty")
expect(contains_only_digits("")).to_equal(false)
```

</details>

#### returns false when has letters

- returns false when has letters
- Verify: returns false when has letters
   - Expected: contains_only_digits("12a") is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("returns false when has letters")
step("Verify: returns false when has letters")
expect(contains_only_digits("12a")).to_equal(false)
```

</details>

### validation - contains_whitespace

#### returns true for space

- returns true for space
- Verify: returns true for space
   - Expected: contains_whitespace("hello world") is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("returns true for space")
step("Verify: returns true for space")
expect(contains_whitespace("hello world")).to_equal(true)
```

</details>

#### returns true for tab

- returns true for tab
- Verify: returns true for tab
   - Expected: contains_whitespace("hello\tworld") is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("returns true for tab")
step("Verify: returns true for tab")
expect(contains_whitespace("hello\tworld")).to_equal(true)
```

</details>

#### returns false for no whitespace

- returns false for no whitespace
- Verify: returns false for no whitespace
   - Expected: contains_whitespace("helloworld") is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("returns false for no whitespace")
step("Verify: returns false for no whitespace")
expect(contains_whitespace("helloworld")).to_equal(false)
```

</details>

#### returns false for empty string

- returns false for empty string
- Verify: returns false for empty string
   - Expected: contains_whitespace("") is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("returns false for empty string")
step("Verify: returns false for empty string")
expect(contains_whitespace("")).to_equal(false)
```

</details>

### validation - starts_with_letter

#### returns true for lowercase start

- returns true for lowercase start
- Verify: returns true for lowercase start
   - Expected: starts_with_letter("abc") is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("returns true for lowercase start")
step("Verify: returns true for lowercase start")
expect(starts_with_letter("abc")).to_equal(true)
```

</details>

#### returns true for uppercase start

- returns true for uppercase start
- Verify: returns true for uppercase start
   - Expected: starts_with_letter("Abc") is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("returns true for uppercase start")
step("Verify: returns true for uppercase start")
expect(starts_with_letter("Abc")).to_equal(true)
```

</details>

#### returns false for digit start

- returns false for digit start
- Verify: returns false for digit start
   - Expected: starts_with_letter("1abc") is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("returns false for digit start")
step("Verify: returns false for digit start")
expect(starts_with_letter("1abc")).to_equal(false)
```

</details>

#### returns false for empty string

- returns false for empty string
- Verify: returns false for empty string
   - Expected: starts_with_letter("") is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("returns false for empty string")
step("Verify: returns false for empty string")
expect(starts_with_letter("")).to_equal(false)
```

</details>

#### returns false for underscore start

- returns false for underscore start
- Verify: returns false for underscore start
   - Expected: starts_with_letter("_abc") is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("returns false for underscore start")
step("Verify: returns false for underscore start")
expect(starts_with_letter("_abc")).to_equal(false)
```

</details>

### validation - is_valid_version

#### returns true for semver

- returns true for semver
- Verify: returns true for semver
   - Expected: is_valid_version("1.2.3") is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("returns true for semver")
step("Verify: returns true for semver")
expect(is_valid_version("1.2.3")).to_equal(true)
```

</details>

#### returns true for two-part version

- returns true for two-part version
- Verify: returns true for two-part version
   - Expected: is_valid_version("1.0") is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("returns true for two-part version")
step("Verify: returns true for two-part version")
expect(is_valid_version("1.0")).to_equal(true)
```

</details>

#### returns false for empty

- returns false for empty
- Verify: returns false for empty
   - Expected: is_valid_version("") is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("returns false for empty")
step("Verify: returns false for empty")
expect(is_valid_version("")).to_equal(false)
```

</details>

#### returns false for no dot

- returns false for no dot
- Verify: returns false for no dot
   - Expected: is_valid_version("123") is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("returns false for no dot")
step("Verify: returns false for no dot")
expect(is_valid_version("123")).to_equal(false)
```

</details>

#### returns false for only dots

- returns false for only dots
- Verify: returns false for only dots
   - Expected: is_valid_version("...") is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("returns false for only dots")
step("Verify: returns false for only dots")
expect(is_valid_version("...")).to_equal(false)
```

</details>

#### returns false for letters

- returns false for letters
- Verify: returns false for letters
   - Expected: is_valid_version("1.2.a") is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("returns false for letters")
step("Verify: returns false for letters")
expect(is_valid_version("1.2.a")).to_equal(false)
```

</details>

### validation - is_valid_path_component

#### returns true for valid name

- returns true for valid name
- Verify: returns true for valid name
   - Expected: is_valid_path_component("myfile") is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("returns true for valid name")
step("Verify: returns true for valid name")
expect(is_valid_path_component("myfile")).to_equal(true)
```

</details>

#### returns false for empty

- returns false for empty
- Verify: returns false for empty
   - Expected: is_valid_path_component("") is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("returns false for empty")
step("Verify: returns false for empty")
expect(is_valid_path_component("")).to_equal(false)
```

</details>

#### returns false for dot start

- returns false for dot start
- Verify: returns false for dot start
   - Expected: is_valid_path_component(".hidden") is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("returns false for dot start")
step("Verify: returns false for dot start")
expect(is_valid_path_component(".hidden")).to_equal(false)
```

</details>

#### returns false for forward slash

- returns false for forward slash
- Verify: returns false for forward slash
   - Expected: is_valid_path_component("path/to") is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("returns false for forward slash")
step("Verify: returns false for forward slash")
expect(is_valid_path_component("path/to")).to_equal(false)
```

</details>

#### returns false for backslash

- returns false for backslash
- Verify: returns false for backslash
   - Expected: is_valid_path_component("path\\to") is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("returns false for backslash")
step("Verify: returns false for backslash")
expect(is_valid_path_component("path\\to")).to_equal(false)
```

</details>

### validation - require

#### returns nil when condition is true

- returns nil when condition is true
- Verify: returns nil when condition is true
   - Expected: result equals `nil`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("returns nil when condition is true")
step("Verify: returns nil when condition is true")
val result = require(true, "error msg")
expect(result).to_equal(nil)
```

</details>

#### returns Some message when condition is false

- returns Some message when condition is false
- Verify: returns Some message when condition is false
   - Expected: result.unwrap() equals `must be valid`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("returns Some message when condition is false")
step("Verify: returns Some message when condition is false")
val result = require(false, "must be valid")
expect(result.unwrap()).to_equal("must be valid")
```

</details>

### validation - require_all

#### returns empty array when all conditions pass

- returns empty array when all conditions pass
- Verify: returns empty array when all conditions pass
   - Expected: errors.len() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("returns empty array when all conditions pass")
step("Verify: returns empty array when all conditions pass")
val errors = require_all([(true, "err1"), (true, "err2")])
expect(errors.len()).to_equal(0)  # oracle: 0 — named expected value from the requirement
```

</details>

#### collects messages for failed conditions

- collects messages for failed conditions
- Verify: collects messages for failed conditions
   - Expected: errors.len() equals `2`
   - Expected: errors[0] equals `err1`
   - Expected: errors[1] equals `err3`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("collects messages for failed conditions")
step("Verify: collects messages for failed conditions")
val errors = require_all([(false, "err1"), (true, "ok"), (false, "err3")])
expect(errors.len()).to_equal(2)  # oracle: 2 — named expected value from the requirement
expect(errors[0]).to_equal("err1")
expect(errors[1]).to_equal("err3")
```

</details>

#### returns all messages when all fail

- returns all messages when all fail
- Verify: returns all messages when all fail
   - Expected: errors.len() equals `2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("returns all messages when all fail")
step("Verify: returns all messages when all fail")
val errors = require_all([(false, "a"), (false, "b")])
expect(errors.len()).to_equal(2)  # oracle: 2 — named expected value from the requirement
```

</details>

### Result enum - Ok and Err

#### Ok creates result with value

- Ok creates result with value
- Verify: Ok creates result with value
   - Expected: r.is_ok() is true
   - Expected: r.unwrap() equals `42`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("Ok creates result with value")
step("Verify: Ok creates result with value")
val r = Ok(42)
expect(r.is_ok()).to_equal(true)
expect(r.unwrap()).to_equal(42)  # oracle: 42 — named expected value from the requirement
```

</details>

#### Err creates result with error

- Err creates result with error
- Verify: Err creates result with error
   - Expected: r.is_err() is true
   - Expected: r.unwrap_err() equals `bad`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("Err creates result with error")
step("Verify: Err creates result with error")
val r = Err("bad")
expect(r.is_err()).to_equal(true)
expect(r.unwrap_err()).to_equal("bad")
```

</details>

### Result enum - is_ok

#### returns true for Ok

- returns true for Ok
- Verify: returns true for Ok
   - Expected: Ok(42).is_ok() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("returns true for Ok")
step("Verify: returns true for Ok")
expect(Ok(42).is_ok()).to_equal(true)
```

</details>

#### returns false for Err

- returns false for Err
- Verify: returns false for Err
   - Expected: Err("e").is_ok() is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("returns false for Err")
step("Verify: returns false for Err")
expect(Err("e").is_ok()).to_equal(false)
```

</details>

### Result enum - is_err

#### returns true for Err

- returns true for Err
- Verify: returns true for Err
   - Expected: Err("e").is_err() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("returns true for Err")
step("Verify: returns true for Err")
expect(Err("e").is_err()).to_equal(true)
```

</details>

#### returns false for Ok

- returns false for Ok
- Verify: returns false for Ok
   - Expected: Ok(42).is_err() is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("returns false for Ok")
step("Verify: returns false for Ok")
expect(Ok(42).is_err()).to_equal(false)
```

</details>

### Result enum - unwrap_or

#### returns Ok value when Ok

- returns Ok value when Ok
- Verify: returns Ok value when Ok
   - Expected: Ok(42).unwrap_or(0) equals `42`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("returns Ok value when Ok")
step("Verify: returns Ok value when Ok")
expect(Ok(42).unwrap_or(0)).to_equal(42)  # oracle: 42 — named expected value from the requirement
```

</details>

#### returns default when Err

- returns default when Err
- Verify: returns default when Err
   - Expected: Err("e").unwrap_or(0) equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("returns default when Err")
step("Verify: returns default when Err")
expect(Err("e").unwrap_or(0)).to_equal(0)
```

</details>

### Result enum - unwrap

#### returns Ok value

- returns Ok value
- Verify: returns Ok value
   - Expected: Ok(42).unwrap() equals `42`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("returns Ok value")
step("Verify: returns Ok value")
expect(Ok(42).unwrap()).to_equal(42)  # oracle: 42 — named expected value from the requirement
```

</details>

### Result enum - unwrap_err

#### returns Err value

- returns Err value
- Verify: returns Err value
   - Expected: Err("bad").unwrap_err() equals `bad`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("returns Err value")
step("Verify: returns Err value")
expect(Err("bad").unwrap_err()).to_equal("bad")
```

</details>

### Result enum - unwrap_or_else

#### returns Ok value when Ok

- returns Ok value when Ok
- Verify: returns Ok value when Ok
   - Expected: Ok(42).unwrap_or_else(\_: 0) equals `42`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("returns Ok value when Ok")
step("Verify: returns Ok value when Ok")
expect(Ok(42).unwrap_or_else(\_: 0)).to_equal(42)  # oracle: 42 — named expected value from the requirement
```

</details>

#### calls function when Err

- calls function when Err
- Verify: calls function when Err
   - Expected: Err("e").unwrap_or_else(\_: 99) equals `99`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("calls function when Err")
step("Verify: calls function when Err")
expect(Err("e").unwrap_or_else(\_: 99)).to_equal(99)
```

</details>

### Result enum - map

#### maps Ok value

- maps Ok value
- Verify: maps Ok value
   - Expected: r.is_ok() is true
   - Expected: r.unwrap() equals `10`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("maps Ok value")
step("Verify: maps Ok value")
val r = Ok(5).map(_1 * 2)
expect(r.is_ok()).to_equal(true)
expect(r.unwrap()).to_equal(10)  # oracle: 10 — named expected value from the requirement
```

</details>

#### passes through Err

- passes through Err
- Verify: passes through Err
   - Expected: r.is_err() is true
   - Expected: r.unwrap_err() equals `e`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("passes through Err")
step("Verify: passes through Err")
val r = Err("e").map(_1 * 2)
expect(r.is_err()).to_equal(true)
expect(r.unwrap_err()).to_equal("e")
```

</details>

### Result enum - map_err

#### maps Err value

- maps Err value
- Verify: maps Err value
   - Expected: r.is_err() is true
   - Expected: r.unwrap_err() equals `Error: io`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("maps Err value")
step("Verify: maps Err value")
val r = Err("io").map_err("Error: " + _1)
expect(r.is_err()).to_equal(true)
expect(r.unwrap_err()).to_equal("Error: io")
```

</details>

#### passes through Ok

- passes through Ok
- Verify: passes through Ok
   - Expected: r.is_ok() is true
   - Expected: r.unwrap() equals `5`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("passes through Ok")
step("Verify: passes through Ok")
val r = Ok(5).map_err("Error: " + _1)
expect(r.is_ok()).to_equal(true)
expect(r.unwrap()).to_equal(5)  # oracle: 5 — named expected value from the requirement
```

</details>

### Result enum - map then flatten

#### flat maps Ok value via map+flatten

- flat maps Ok value via map+flatten
- Verify: flat maps Ok value via map+flatten
   - Expected: r.unwrap() equals `10`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("flat maps Ok value via map+flatten")
step("Verify: flat maps Ok value via map+flatten")
val mapped = Ok(5).map(Ok(_1 * 2))
val r = mapped.flatten()
expect(r.unwrap()).to_equal(10)  # oracle: 10 — named expected value from the requirement
```

</details>

#### flat maps Ok to Err via map+flatten

- flat maps Ok to Err via map+flatten
- Verify: flat maps Ok to Err via map+flatten
   - Expected: r.is_err() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("flat maps Ok to Err via map+flatten")
step("Verify: flat maps Ok to Err via map+flatten")
val mapped = Ok(5).map(\_: Err("bad"))
val r = mapped.flatten()
expect(r.is_err()).to_equal(true)
```

</details>

#### passes through Err with map

- passes through Err with map
- Verify: passes through Err with map
   - Expected: r.is_err() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("passes through Err with map")
step("Verify: passes through Err with map")
val r = Err("e").map(Ok(_1 * 2))
expect(r.is_err()).to_equal(true)
```

</details>

### Result enum - or

#### returns first when first is Ok

- returns first when first is Ok
- Verify: returns first when first is Ok
   - Expected: r.unwrap() equals `5`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("returns first when first is Ok")
step("Verify: returns first when first is Ok")
val r = Ok(5).or(Ok(10))
expect(r.unwrap()).to_equal(5)  # oracle: 5 — named expected value from the requirement
```

</details>

#### returns second when first is Err

- returns second when first is Err
- Verify: returns second when first is Err
   - Expected: r.unwrap() equals `10`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("returns second when first is Err")
step("Verify: returns second when first is Err")
val r = Err("e").or(Ok(10))
expect(r.unwrap()).to_equal(10)  # oracle: 10 — named expected value from the requirement
```

</details>

#### returns second Err when both Err

- returns second Err when both Err
- Verify: returns second Err when both Err
   - Expected: r.unwrap_err() equals `e2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("returns second Err when both Err")
step("Verify: returns second Err when both Err")
val r = Err("e1").or(Err("e2"))
expect(r.unwrap_err()).to_equal("e2")
```

</details>

### Result enum - or_else

#### returns Ok when Ok

- returns Ok when Ok
- Verify: returns Ok when Ok
   - Expected: r.unwrap() equals `5`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("returns Ok when Ok")
step("Verify: returns Ok when Ok")
val r = Ok(5).or_else(\_: Ok(0))
expect(r.unwrap()).to_equal(5)  # oracle: 5 — named expected value from the requirement
```

</details>

#### calls function when Err

- calls function when Err
- Verify: calls function when Err
   - Expected: r.unwrap() equals `99`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("calls function when Err")
step("Verify: calls function when Err")
val r = Err("e").or_else(\_: Ok(99))
expect(r.unwrap()).to_equal(99)  # oracle: 99 — named expected value from the requirement
```

</details>

### Result enum - flatten

#### flattens Ok(Ok(v)) to Ok(v)

- flattens Ok(Ok(v)) to Ok(v)
- Verify: flattens Ok(Ok(v)) to Ok(v)
   - Expected: r.unwrap() equals `5`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("flattens Ok(Ok(v)) to Ok(v)")
step("Verify: flattens Ok(Ok(v)) to Ok(v)")
val r = Ok(Ok(5)).flatten()
expect(r.unwrap()).to_equal(5)  # oracle: 5 — named expected value from the requirement
```

</details>

#### flattens Ok(Err(e)) to Err(e)

- flattens Ok(Err(e)) to Err(e)
- Verify: flattens Ok(Err(e)) to Err(e)
   - Expected: r.is_err() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("flattens Ok(Err(e)) to Err(e)")
step("Verify: flattens Ok(Err(e)) to Err(e)")
val r = Ok(Err("e")).flatten()
expect(r.is_err()).to_equal(true)
```

</details>

#### passes through outer Err

- passes through outer Err
- Verify: passes through outer Err
   - Expected: r.is_err() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("passes through outer Err")
step("Verify: passes through outer Err")
val r = Err("outer").flatten()
expect(r.is_err()).to_equal(true)
```

</details>

### Result enum - unwrap_or with Err

#### returns default for Err via unwrap_or

- returns default for Err via unwrap_or
- Verify: returns default for Err via unwrap_or
   - Expected: r.unwrap_or(99) equals `99`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("returns default for Err via unwrap_or")
step("Verify: returns default for Err via unwrap_or")
val r = Err("e")
expect(r.unwrap_or(99)).to_equal(99)  # oracle: 99 — named expected value from the requirement
```

</details>

#### returns value for Ok via unwrap_or

- returns value for Ok via unwrap_or
- Verify: returns value for Ok via unwrap_or
   - Expected: r.unwrap_or(99) equals `5`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("returns value for Ok via unwrap_or")
step("Verify: returns value for Ok via unwrap_or")
val r = Ok(5)
expect(r.unwrap_or(99)).to_equal(5)  # oracle: 5 — named expected value from the requirement
```

</details>

### Result enum - ok

#### returns Some(value) for Ok

- returns Some(value) for Ok
- Verify: returns Some(value) for Ok
   - Expected: opt.unwrap() equals `42`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("returns Some(value) for Ok")
step("Verify: returns Some(value) for Ok")
val opt = Ok(42).ok()
expect(opt.unwrap()).to_equal(42)  # oracle: 42 — named expected value from the requirement
```

</details>

#### returns None for Err

- returns None for Err
- Verify: returns None for Err
   - Expected: opt == nil is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("returns None for Err")
step("Verify: returns None for Err")
val opt = Err("e").ok()
expect(opt == nil).to_equal(true)
```

</details>

### Result enum - err

#### returns Some(error) for Err

- returns Some(error) for Err
- Verify: returns Some(error) for Err
   - Expected: opt.unwrap() equals `bad`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("returns Some(error) for Err")
step("Verify: returns Some(error) for Err")
val opt = Err("bad").err()
expect(opt.unwrap()).to_equal("bad")
```

</details>

#### returns None for Ok

- returns None for Ok
- Verify: returns None for Ok
   - Expected: opt == nil is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("returns None for Ok")
step("Verify: returns None for Ok")
val opt = Ok(42).err()
expect(opt == nil).to_equal(true)
```

</details>

### Result enum - expect

#### returns Ok value with expect

- returns Ok value with expect
- Verify: returns Ok value with expect
   - Expected: Ok(42).expect("should be ok") equals `42`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("returns Ok value with expect")
step("Verify: returns Ok value with expect")
expect(Ok(42).expect("should be ok")).to_equal(42)
```

</details>

### Result enum - expect_err

#### returns Err value with expect_err

- returns Err value with expect_err
- Verify: returns Err value with expect_err
   - Expected: Err("bad").expect_err("should be err") equals `bad`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("returns Err value with expect_err")
step("Verify: returns Err value with expect_err")
expect(Err("bad").expect_err("should be err")).to_equal("bad")
```

</details>

### Result enum - map_err chaining

#### maps error and checks original Ok preserved

- maps error and checks original Ok preserved
- Verify: maps error and checks original Ok preserved
   - Expected: r.is_ok() is true
   - Expected: r.unwrap() equals `10`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("maps error and checks original Ok preserved")
step("Verify: maps error and checks original Ok preserved")
val r = Ok(10).map_err("wrapped: " + _1)
expect(r.is_ok()).to_equal(true)
expect(r.unwrap()).to_equal(10)  # oracle: 10 — named expected value from the requirement
```

</details>

#### maps error message on Err

- maps error message on Err
- Verify: maps error message on Err
   - Expected: r.is_err() is true
   - Expected: r.unwrap_err() equals `wrapped: timeout`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("maps error message on Err")
step("Verify: maps error message on Err")
val r = Err("timeout").map_err("wrapped: " + _1)
expect(r.is_err()).to_equal(true)
expect(r.unwrap_err()).to_equal("wrapped: timeout")
```

</details>

### Result enum - or_else chaining

#### returns recovery value on Err

- returns recovery value on Err
- Verify: returns recovery value on Err
   - Expected: r.is_err() is true
   - Expected: r.unwrap_err() equals `fallback`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("returns recovery value on Err")
step("Verify: returns recovery value on Err")
val r = Err("first").or_else(\_: Err("fallback"))
expect(r.is_err()).to_equal(true)
expect(r.unwrap_err()).to_equal("fallback")
```

</details>

#### ignores or_else on Ok

- ignores or_else on Ok
- Verify: ignores or_else on Ok
   - Expected: r.unwrap() equals `42`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("ignores or_else on Ok")
step("Verify: ignores or_else on Ok")
val r = Ok(42).or_else(\_: Ok(0))
expect(r.unwrap()).to_equal(42)  # oracle: 42 — named expected value from the requirement
```

</details>

### Result enum - flatten nested

#### flattens nested Ok

- flattens nested Ok
- Verify: flattens nested Ok
   - Expected: r.unwrap() equals `100`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("flattens nested Ok")
step("Verify: flattens nested Ok")
val r = Ok(Ok(100)).flatten()
expect(r.unwrap()).to_equal(100)  # oracle: 100 — named expected value from the requirement
```

</details>

#### flattens nested Err inside Ok

- flattens nested Err inside Ok
- Verify: flattens nested Err inside Ok
   - Expected: r.is_err() is true
   - Expected: r.unwrap_err() equals `inner`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("flattens nested Err inside Ok")
step("Verify: flattens nested Err inside Ok")
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

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-LIB`
- `REQ-LIB-COMMON-001`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `11f409c45ad2e04fcff083bec3e18f434140c30d18aeecfdacfd2d5430c06bcc`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `11f409c45ad2e04fcff083bec3e18f434140c30d18aeecfdacfd2d5430c06bcc`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `11f409c45ad2e04fcff083bec3e18f434140c30d18aeecfdacfd2d5430c06bcc`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **86/100**; effective score: **86/100**; blockers: **0**.

SSpec documentization score: 86/100
source: test/01_unit/lib/common/validation_coverage_spec.spl
mirror: doc/06_spec/01_unit/lib/common/validation_coverage_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/lib/common/validation_coverage_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/lib/common/validation_coverage_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: scope, assumptions/preconditions, primary workflow, evidence, unsupported/limitations
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/lib/common/validation_coverage_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 3 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/lib/common/validation_coverage_spec.spl:78:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'accepts lowercase letter start' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/common/validation_coverage_spec.spl:85:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'accepts underscore start' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/common/validation_coverage_spec.spl:91:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'accepts uppercase start' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
