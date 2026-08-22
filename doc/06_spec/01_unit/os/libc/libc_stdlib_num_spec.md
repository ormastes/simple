# libc_stdlib_num_spec

> Verifies the libc stdlib num behaviour end to end so maintainers of this

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 41 | 41 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# libc_stdlib_num_spec

Verifies the libc stdlib num behaviour end to end so maintainers of this

## At a Glance

| Field | Value |
|-------|-------|
| Category | Hardware & OS |
| Status | Active |
| Source | `test/01_unit/os/libc/libc_stdlib_num_spec.spl` |
| Updated | 2026-08-22 |
| Generator | `simple spipe-docgen` (Simple) |

## Purpose and audience
Verifies the libc stdlib num behaviour end to end so maintainers of this
component and reviewers of its spec share one pinned definition.
## Operator workflow
Run `bin/simple test <this spec>`; read the per-scenario verdicts in
the `Results:` summary. Each scenario asserts an observable outcome.
## Compatibility and limitations
Covers the currently shipped behaviour only; performance, stress and
unrelated sibling features are out of scope.

## Scenarios

### SimpleOS libc stdlib numeric (integer)

### libc_strtoul — unsigned parse

#### parses simple decimal

- Verify: parses simple decimal
   - Expected: libc_strtoul("123".bytes(), 10) equals `123)  # oracle: pinned constant asserted by this scenario`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-OS-LIBC_LIBC_STDLIB_NUM-001
step("Verify: parses simple decimal")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
expect(libc_strtoul("123".bytes(), 10)).to_equal(123)  # oracle: pinned constant asserted by this scenario
```

</details>

#### parses hex with 0x prefix auto-detect

- Verify: parses hex with 0x prefix auto-detect
   - Expected: libc_strtoul("0xFF".bytes(), 0) equals `255)  # oracle: pinned constant asserted by this scenario`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-OS-LIBC_LIBC_STDLIB_NUM-001
step("Verify: parses hex with 0x prefix auto-detect")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
expect(libc_strtoul("0xFF".bytes(), 0)).to_equal(255)  # oracle: pinned constant asserted by this scenario
```

</details>

#### parses octal with 0 prefix auto-detect

- Verify: parses octal with 0 prefix auto-detect
   - Expected: libc_strtoul("017".bytes(), 0) equals `15)  # oracle: pinned constant asserted by this scenario`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-OS-LIBC_LIBC_STDLIB_NUM-001
step("Verify: parses octal with 0 prefix auto-detect")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
expect(libc_strtoul("017".bytes(), 0)).to_equal(15)  # oracle: pinned constant asserted by this scenario
```

</details>

#### parses decimal with base 0 (no prefix)

- Verify: parses decimal with base 0 (no prefix)
   - Expected: libc_strtoul("42".bytes(), 0) equals `42)  # oracle: pinned constant asserted by this scenario`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-OS-LIBC_LIBC_STDLIB_NUM-001
step("Verify: parses decimal with base 0 (no prefix)")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
expect(libc_strtoul("42".bytes(), 0)).to_equal(42)  # oracle: pinned constant asserted by this scenario
```

</details>

#### skips leading whitespace

- Verify: skips leading whitespace
   - Expected: libc_strtoul("  42".bytes(), 10) equals `42)  # oracle: pinned constant asserted by this scenario`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-OS-LIBC_LIBC_STDLIB_NUM-001
step("Verify: skips leading whitespace")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
expect(libc_strtoul("  42".bytes(), 10)).to_equal(42)  # oracle: pinned constant asserted by this scenario
```

</details>

#### stops at first non-digit

- Verify: stops at first non-digit
   - Expected: libc_strtoul("42abc".bytes(), 10) equals `42)  # oracle: pinned constant asserted by this scenario`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-OS-LIBC_LIBC_STDLIB_NUM-001
step("Verify: stops at first non-digit")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
expect(libc_strtoul("42abc".bytes(), 10)).to_equal(42)  # oracle: pinned constant asserted by this scenario
```

</details>

#### handles empty input

- Verify: handles empty input
   - Expected: libc_strtoul("".bytes(), 10) equals `0)  # oracle: pinned constant asserted by this scenario`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-OS-LIBC_LIBC_STDLIB_NUM-001
step("Verify: handles empty input")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
expect(libc_strtoul("".bytes(), 10)).to_equal(0)  # oracle: pinned constant asserted by this scenario
```

</details>

#### handles non-numeric input

- Verify: handles non-numeric input
   - Expected: libc_strtoul("abc".bytes(), 10) equals `0)  # oracle: pinned constant asserted by this scenario`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-OS-LIBC_LIBC_STDLIB_NUM-001
step("Verify: handles non-numeric input")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
expect(libc_strtoul("abc".bytes(), 10)).to_equal(0)  # oracle: pinned constant asserted by this scenario
```

</details>

#### parses base 16 explicit

- Verify: parses base 16 explicit
   - Expected: libc_strtoul("FF".bytes(), 16) equals `255)  # oracle: pinned constant asserted by this scenario`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-OS-LIBC_LIBC_STDLIB_NUM-001
step("Verify: parses base 16 explicit")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
expect(libc_strtoul("FF".bytes(), 16)).to_equal(255)  # oracle: pinned constant asserted by this scenario
```

</details>

#### parses base 2

- Verify: parses base 2
   - Expected: libc_strtoul("1010".bytes(), 2) equals `10)  # oracle: pinned constant asserted by this scenario`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-OS-LIBC_LIBC_STDLIB_NUM-001
step("Verify: parses base 2")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
expect(libc_strtoul("1010".bytes(), 2)).to_equal(10)  # oracle: pinned constant asserted by this scenario
```

</details>

#### accepts a leading minus and negates (C-conformant)

- Verify: accepts a leading minus and negates (C-conformant)
   - Expected: libc_strtoul("-1".bytes(), 10) equals `-1)  # oracle: pinned constant asserted by this scenario`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-OS-LIBC_LIBC_STDLIB_NUM-001
step("Verify: accepts a leading minus and negates (C-conformant)")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
expect(libc_strtoul("-1".bytes(), 10)).to_equal(-1)  # oracle: pinned constant asserted by this scenario
```

</details>

#### accepts a leading plus

- Verify: accepts a leading plus
   - Expected: libc_strtoul("+5".bytes(), 10) equals `5)  # oracle: pinned constant asserted by this scenario`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-OS-LIBC_LIBC_STDLIB_NUM-001
step("Verify: accepts a leading plus")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
expect(libc_strtoul("+5".bytes(), 10)).to_equal(5)  # oracle: pinned constant asserted by this scenario
```

</details>

#### base-0 bare zero is 0

- Verify: base-0 bare zero is 0
   - Expected: libc_strtoul("0".bytes(), 0) equals `0)  # oracle: pinned constant asserted by this scenario`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-OS-LIBC_LIBC_STDLIB_NUM-001
step("Verify: base-0 bare zero is 0")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
expect(libc_strtoul("0".bytes(), 0)).to_equal(0)  # oracle: pinned constant asserted by this scenario
```

</details>

#### base-0 '0x' with no hex digit is 0

- Verify: base-0 '0x' with no hex digit is 0
   - Expected: libc_strtoul("0x".bytes(), 0) equals `0)  # oracle: pinned constant asserted by this scenario`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-OS-LIBC_LIBC_STDLIB_NUM-001
step("Verify: base-0 '0x' with no hex digit is 0")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
expect(libc_strtoul("0x".bytes(), 0)).to_equal(0)  # oracle: pinned constant asserted by this scenario
```

</details>

#### base-0 '08' stops at invalid octal digit

- Verify: base-0 '08' stops at invalid octal digit
   - Expected: libc_strtoul("08".bytes(), 0) equals `0)  # oracle: pinned constant asserted by this scenario`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-OS-LIBC_LIBC_STDLIB_NUM-001
step("Verify: base-0 '08' stops at invalid octal digit")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
expect(libc_strtoul("08".bytes(), 0)).to_equal(0)  # oracle: pinned constant asserted by this scenario
```

</details>

### libc_strtoll — signed parse

#### parses simple decimal

- Verify: parses simple decimal
   - Expected: libc_strtoll("123".bytes(), 10) equals `123)  # oracle: pinned constant asserted by this scenario`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-OS-LIBC_LIBC_STDLIB_NUM-001
step("Verify: parses simple decimal")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
expect(libc_strtoll("123".bytes(), 10)).to_equal(123)  # oracle: pinned constant asserted by this scenario
```

</details>

#### parses negative

- Verify: parses negative
   - Expected: libc_strtoll("-42".bytes(), 10) equals `-42)  # oracle: pinned constant asserted by this scenario`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-OS-LIBC_LIBC_STDLIB_NUM-001
step("Verify: parses negative")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
expect(libc_strtoll("-42".bytes(), 10)).to_equal(-42)  # oracle: pinned constant asserted by this scenario
```

</details>

#### parses positive sign

- Verify: parses positive sign
   - Expected: libc_strtoll("+42".bytes(), 10) equals `42)  # oracle: pinned constant asserted by this scenario`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-OS-LIBC_LIBC_STDLIB_NUM-001
step("Verify: parses positive sign")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
expect(libc_strtoll("+42".bytes(), 10)).to_equal(42)  # oracle: pinned constant asserted by this scenario
```

</details>

#### parses negative hex

- Verify: parses negative hex
   - Expected: libc_strtoll("-0xFF".bytes(), 0) equals `-255)  # oracle: pinned constant asserted by this scenario`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-OS-LIBC_LIBC_STDLIB_NUM-001
step("Verify: parses negative hex")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
expect(libc_strtoll("-0xFF".bytes(), 0)).to_equal(-255)  # oracle: pinned constant asserted by this scenario
```

</details>

#### skips leading whitespace with sign

- Verify: skips leading whitespace with sign
   - Expected: libc_strtoll("  -42".bytes(), 10) equals `-42)  # oracle: pinned constant asserted by this scenario`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-OS-LIBC_LIBC_STDLIB_NUM-001
step("Verify: skips leading whitespace with sign")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
expect(libc_strtoll("  -42".bytes(), 10)).to_equal(-42)  # oracle: pinned constant asserted by this scenario
```

</details>

#### stops at first non-digit

- Verify: stops at first non-digit
   - Expected: libc_strtoll("-42xyz".bytes(), 10) equals `-42)  # oracle: pinned constant asserted by this scenario`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-OS-LIBC_LIBC_STDLIB_NUM-001
step("Verify: stops at first non-digit")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
expect(libc_strtoll("-42xyz".bytes(), 10)).to_equal(-42)  # oracle: pinned constant asserted by this scenario
```

</details>

#### handles empty input

- Verify: handles empty input
   - Expected: libc_strtoll("".bytes(), 10) equals `0)  # oracle: pinned constant asserted by this scenario`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-OS-LIBC_LIBC_STDLIB_NUM-001
step("Verify: handles empty input")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
expect(libc_strtoll("".bytes(), 10)).to_equal(0)  # oracle: pinned constant asserted by this scenario
```

</details>

#### parses negative octal

- Verify: parses negative octal
   - Expected: libc_strtoll("-017".bytes(), 0) equals `-15)  # oracle: pinned constant asserted by this scenario`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-OS-LIBC_LIBC_STDLIB_NUM-001
step("Verify: parses negative octal")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
expect(libc_strtoll("-017".bytes(), 0)).to_equal(-15)  # oracle: pinned constant asserted by this scenario
```

</details>

### libc_strtoull — unsigned long long

#### parses simple decimal

- Verify: parses simple decimal
   - Expected: libc_strtoull("123".bytes(), 10) equals `123)  # oracle: pinned constant asserted by this scenario`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-OS-LIBC_LIBC_STDLIB_NUM-001
step("Verify: parses simple decimal")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
expect(libc_strtoull("123".bytes(), 10)).to_equal(123)  # oracle: pinned constant asserted by this scenario
```

</details>

#### parses hex with auto-detect

- Verify: parses hex with auto-detect
   - Expected: libc_strtoull("0xFF".bytes(), 0) equals `255)  # oracle: pinned constant asserted by this scenario`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-OS-LIBC_LIBC_STDLIB_NUM-001
step("Verify: parses hex with auto-detect")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
expect(libc_strtoull("0xFF".bytes(), 0)).to_equal(255)  # oracle: pinned constant asserted by this scenario
```

</details>

#### large value

- Verify: large value
   - Expected: libc_strtoull("1234567890".bytes(), 10) equals `1234567890)  # oracle: pinned constant asserted by this scenario`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-OS-LIBC_LIBC_STDLIB_NUM-001
step("Verify: large value")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
expect(libc_strtoull("1234567890".bytes(), 10)).to_equal(1234567890)  # oracle: pinned constant asserted by this scenario
```

</details>

### libc_div — integer division

#### divides positive by positive

- Verify: divides positive by positive
   - Expected: result.quot equals `3)  # oracle: pinned constant asserted by this scenario`
   - Expected: result.rem equals `1)  # oracle: pinned constant asserted by this scenario`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-OS-LIBC_LIBC_STDLIB_NUM-001
step("Verify: divides positive by positive")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
val result = libc_div(7, 2)
expect(result.quot).to_equal(3)  # oracle: pinned constant asserted by this scenario
expect(result.rem).to_equal(1)  # oracle: pinned constant asserted by this scenario
```

</details>

#### divides negative by positive (toward zero)

- Verify: divides negative by positive (toward zero)
   - Expected: result.quot equals `-3)  # oracle: pinned constant asserted by this scenario`
   - Expected: result.rem equals `-1)  # oracle: pinned constant asserted by this scenario`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-OS-LIBC_LIBC_STDLIB_NUM-001
step("Verify: divides negative by positive (toward zero)")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
val result = libc_div(-7, 2)
expect(result.quot).to_equal(-3)  # oracle: pinned constant asserted by this scenario
expect(result.rem).to_equal(-1)  # oracle: pinned constant asserted by this scenario
```

</details>

#### divides positive by negative (toward zero)

- Verify: divides positive by negative (toward zero)
   - Expected: result.quot equals `-3)  # oracle: pinned constant asserted by this scenario`
   - Expected: result.rem equals `1)  # oracle: pinned constant asserted by this scenario`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-OS-LIBC_LIBC_STDLIB_NUM-001
step("Verify: divides positive by negative (toward zero)")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
val result = libc_div(7, -2)
expect(result.quot).to_equal(-3)  # oracle: pinned constant asserted by this scenario
expect(result.rem).to_equal(1)  # oracle: pinned constant asserted by this scenario
```

</details>

#### divides negative by negative

- Verify: divides negative by negative
   - Expected: result.quot equals `3)  # oracle: pinned constant asserted by this scenario`
   - Expected: result.rem equals `-1)  # oracle: pinned constant asserted by this scenario`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-OS-LIBC_LIBC_STDLIB_NUM-001
step("Verify: divides negative by negative")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
val result = libc_div(-7, -2)
expect(result.quot).to_equal(3)  # oracle: pinned constant asserted by this scenario
expect(result.rem).to_equal(-1)  # oracle: pinned constant asserted by this scenario
```

</details>

#### exact division has zero remainder

- Verify: exact division has zero remainder
   - Expected: result.quot equals `5)  # oracle: pinned constant asserted by this scenario`
   - Expected: result.rem equals `0)  # oracle: pinned constant asserted by this scenario`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-OS-LIBC_LIBC_STDLIB_NUM-001
step("Verify: exact division has zero remainder")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
val result = libc_div(10, 2)
expect(result.quot).to_equal(5)  # oracle: pinned constant asserted by this scenario
expect(result.rem).to_equal(0)  # oracle: pinned constant asserted by this scenario
```

</details>

#### handles zero numerator

- Verify: handles zero numerator
   - Expected: result.quot equals `0)  # oracle: pinned constant asserted by this scenario`
   - Expected: result.rem equals `0)  # oracle: pinned constant asserted by this scenario`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-OS-LIBC_LIBC_STDLIB_NUM-001
step("Verify: handles zero numerator")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
val result = libc_div(0, 5)
expect(result.quot).to_equal(0)  # oracle: pinned constant asserted by this scenario
expect(result.rem).to_equal(0)  # oracle: pinned constant asserted by this scenario
```

</details>

### libc_ldiv — long division

#### long divide matches div

- Verify: long divide matches div
   - Expected: result.quot equals `3)  # oracle: pinned constant asserted by this scenario`
   - Expected: result.rem equals `1)  # oracle: pinned constant asserted by this scenario`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-OS-LIBC_LIBC_STDLIB_NUM-001
step("Verify: long divide matches div")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
val result = libc_ldiv(7, 2)
expect(result.quot).to_equal(3)  # oracle: pinned constant asserted by this scenario
expect(result.rem).to_equal(1)  # oracle: pinned constant asserted by this scenario
```

</details>

#### large numbers

- Verify: large numbers
   - Expected: result.quot equals `333333333)  # oracle: pinned constant asserted by this scenario`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-OS-LIBC_LIBC_STDLIB_NUM-001
step("Verify: large numbers")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
val result = libc_ldiv(1000000000, 3)
expect(result.quot).to_equal(333333333)  # oracle: pinned constant asserted by this scenario
```

</details>

### libc_lldiv — long long division

#### long long divide matches div

- Verify: long long divide matches div
   - Expected: result.quot equals `3)  # oracle: pinned constant asserted by this scenario`
   - Expected: result.rem equals `1)  # oracle: pinned constant asserted by this scenario`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-OS-LIBC_LIBC_STDLIB_NUM-001
step("Verify: long long divide matches div")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
val result = libc_lldiv(7, 2)
expect(result.quot).to_equal(3)  # oracle: pinned constant asserted by this scenario
expect(result.rem).to_equal(1)  # oracle: pinned constant asserted by this scenario
```

</details>

#### large dividend

- Verify: large dividend
   - Expected: result.quot equals `10288065)  # oracle: pinned constant asserted by this scenario`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-OS-LIBC_LIBC_STDLIB_NUM-001
step("Verify: large dividend")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
val result = libc_lldiv(123456789, 12)
expect(result.quot).to_equal(10288065)  # oracle: pinned constant asserted by this scenario
```

</details>

### libc_rand_next — LCG pseudorandom

#### deterministic: same input state yields same output

- Verify: deterministic: same input state yields same output
   - Expected: r1.state equals `r2.state`
   - Expected: r1.value equals `r2.value`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-OS-LIBC_LIBC_STDLIB_NUM-001
step("Verify: deterministic: same input state yields same output")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
val r1 = libc_rand_next(12345)
val r2 = libc_rand_next(12345)
expect(r1.state).to_equal(r2.state)
expect(r1.value).to_equal(r2.value)
```

</details>

#### produces non-zero values from seed

- Verify: produces non-zero values from seed


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-OS-LIBC_LIBC_STDLIB_NUM-001
step("Verify: produces non-zero values from seed")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
val r = libc_rand_next(12345)
expect(r.state).to_be_greater_than(0)
expect(r.value).to_be_greater_than(0)
```

</details>

#### value is always in range 0..32767

- Verify: value is always in range 0..32767


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-OS-LIBC_LIBC_STDLIB_NUM-001
step("Verify: value is always in range 0..32767")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
var state = 12345
var i = 0
while i < 10:
    val r = libc_rand_next(state)
    expect(r.value).to_be_greater_than(-1)
    expect(r.value).to_be_less_than(32768)
    state = r.state
    i = i + 1
```

</details>

#### chain produces different values

- Verify: chain produces different values


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-OS-LIBC_LIBC_STDLIB_NUM-001
step("Verify: chain produces different values")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
val r1 = libc_rand_next(42)
val r2 = libc_rand_next(r1.state)
expect(r2.value).to_be_greater_than(-1)
expect(r2.value).to_be_less_than(32768)
```

</details>

#### different seeds produce different sequences

- Verify: different seeds produce different sequences


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-OS-LIBC_LIBC_STDLIB_NUM-001
step("Verify: different seeds produce different sequences")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
val s1 = libc_rand_next(100).state
val s2 = libc_rand_next(200).state
expect(s1).to_not_equal(s2)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 41 |
| Active scenarios | 41 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `0da24f0947ed50b1acc7b4c0b9390d0d86fd5398f708c4a310e03460300e460a`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `0da24f0947ed50b1acc7b4c0b9390d0d86fd5398f708c4a310e03460300e460a`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `0da24f0947ed50b1acc7b4c0b9390d0d86fd5398f708c4a310e03460300e460a`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **94/100**; effective score: **94/100**; blockers: **0**.

SSpec documentization score: 94/100
source: test/01_unit/os/libc/libc_stdlib_num_spec.spl
mirror: doc/06_spec/01_unit/os/libc/libc_stdlib_num_spec.md (current)
findings: 3 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=85 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/os/libc/libc_stdlib_num_spec.md:1:1: warning SSDOC-EVD-002 [evidence] (-15): source steps are not visible in the generated manual
  why: Source tokens alone do not prove reader-visible workflow structure.
  improve: Use supported literal step calls and regenerate the manual.
doc/06_spec/01_unit/os/libc/libc_stdlib_num_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/os/libc/libc_stdlib_num_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: assumptions/preconditions, traceability, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
<!-- sspec-maintain:scorecard:end -->
