# convert_spec

> Purpose: Prove that std.convert.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 22 | 22 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# convert_spec

Purpose: Prove that std.convert.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/unit/lib/common/convert_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Purpose and audience
Purpose: Prove that std.convert.
Audience: compiler and tooling engineers who maintain this spec.

## Scenarios

### std.convert

### digit_value

#### returns value for digits 0-9

- returns value for digits 0-9
- Verify: returns value for digits 0-9
   - Expected: digit_value("0") equals `0`
   - Expected: digit_value("5") equals `5`
   - Expected: digit_value("9") equals `9`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns value for digits 0-9")
step("Verify: returns value for digits 0-9")
# @req: REQ-LIB-COMMON-001
expect(digit_value("0")).to_equal(0)
expect(digit_value("5")).to_equal(5)
expect(digit_value("9")).to_equal(9)
```

</details>

#### returns -1 for non-digits

- returns -1 for non-digits
- Verify: returns -1 for non-digits
   - Expected: digit_value("a") equals `-1`
   - Expected: digit_value(" ") equals `-1`
   - Expected: digit_value("") equals `-1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns -1 for non-digits")
step("Verify: returns -1 for non-digits")
expect(digit_value("a")).to_equal(-1)
expect(digit_value(" ")).to_equal(-1)
expect(digit_value("")).to_equal(-1)
```

</details>

### safe_parse_int

#### parses positive integers

- parses positive integers
- Verify: parses positive integers
   - Expected: safe_parse_int("42") equals `42`
   - Expected: safe_parse_int("0") equals `0`
   - Expected: safe_parse_int("12345") equals `12345`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("parses positive integers")
step("Verify: parses positive integers")
expect(safe_parse_int("42")).to_equal(42)
expect(safe_parse_int("0")).to_equal(0)
expect(safe_parse_int("12345")).to_equal(12345)
```

</details>

#### parses negative integers

- parses negative integers
- Verify: parses negative integers
   - Expected: safe_parse_int("-1") equals `-1`
   - Expected: safe_parse_int("-999") equals `-999`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("parses negative integers")
step("Verify: parses negative integers")
expect(safe_parse_int("-1")).to_equal(-1)
expect(safe_parse_int("-999")).to_equal(-999)
```

</details>

#### returns 0 for invalid input

- returns 0 for invalid input
- Verify: returns 0 for invalid input
   - Expected: safe_parse_int("") equals `0`
   - Expected: safe_parse_int("abc") equals `0`
   - Expected: safe_parse_int("-") equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns 0 for invalid input")
step("Verify: returns 0 for invalid input")
expect(safe_parse_int("")).to_equal(0)
expect(safe_parse_int("abc")).to_equal(0)
expect(safe_parse_int("-")).to_equal(0)
```

</details>

#### handles whitespace

- handles whitespace
- Verify: handles whitespace
   - Expected: safe_parse_int("  42  ") equals `42`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("handles whitespace")
step("Verify: handles whitespace")
expect(safe_parse_int("  42  ")).to_equal(42)
```

</details>

### parse_u16

#### parses valid u16 values

- parses valid u16 values
- Verify: parses valid u16 values
   - Expected: parse_u16("0") equals `0`
   - Expected: parse_u16("65535") equals `65535`
   - Expected: parse_u16("1000") equals `1000`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("parses valid u16 values")
step("Verify: parses valid u16 values")
expect(parse_u16("0")).to_equal(0)
expect(parse_u16("65535")).to_equal(65535)
expect(parse_u16("1000")).to_equal(1000)
```

</details>

#### returns 0 for out of range

- returns 0 for out of range
- Verify: returns 0 for out of range
   - Expected: parse_u16("65536") equals `0`
   - Expected: parse_u16("-1") equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns 0 for out of range")
step("Verify: returns 0 for out of range")
expect(parse_u16("65536")).to_equal(0)
expect(parse_u16("-1")).to_equal(0)
```

</details>

### parse_u32

#### parses valid u32 values

- parses valid u32 values
- Verify: parses valid u32 values
   - Expected: parse_u32("0") equals `0`
   - Expected: parse_u32("1000000") equals `1000000`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("parses valid u32 values")
step("Verify: parses valid u32 values")
expect(parse_u32("0")).to_equal(0)
expect(parse_u32("1000000")).to_equal(1000000)
```

</details>

#### returns 0 for negative

- returns 0 for negative
- Verify: returns 0 for negative
   - Expected: parse_u32("-1") equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns 0 for negative")
step("Verify: returns 0 for negative")
expect(parse_u32("-1")).to_equal(0)
```

</details>

### parse_u64

#### parses valid positive values

- parses valid positive values
- Verify: parses valid positive values
   - Expected: parse_u64("0") equals `0`
   - Expected: parse_u64("999999999") equals `999999999`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("parses valid positive values")
step("Verify: parses valid positive values")
expect(parse_u64("0")).to_equal(0)
expect(parse_u64("999999999")).to_equal(999999999)
```

</details>

#### returns 0 for negative

- returns 0 for negative
- Verify: returns 0 for negative
   - Expected: parse_u64("-5") equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns 0 for negative")
step("Verify: returns 0 for negative")
expect(parse_u64("-5")).to_equal(0)
```

</details>

### i64_to_usize

#### passes through positive values

- passes through positive values
- Verify: passes through positive values
   - Expected: i64_to_usize(42) equals `42`
   - Expected: i64_to_usize(0) equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("passes through positive values")
step("Verify: passes through positive values")
expect(i64_to_usize(42)).to_equal(42)  # oracle: 42 — named expected value from the requirement
expect(i64_to_usize(0)).to_equal(0)  # oracle: 0 — named expected value from the requirement
```

</details>

#### clamps negatives to 0

- clamps negatives to 0
- Verify: clamps negatives to 0
   - Expected: i64_to_usize(-1) equals `0`
   - Expected: i64_to_usize(-999) equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("clamps negatives to 0")
step("Verify: clamps negatives to 0")
expect(i64_to_usize(-1)).to_equal(0)  # oracle: 0 — named expected value from the requirement
expect(i64_to_usize(-999)).to_equal(0)  # oracle: 0 — named expected value from the requirement
```

</details>

### usize_to_i64

#### is identity operation

- is identity operation
- Verify: is identity operation
   - Expected: usize_to_i64(42) equals `42`
   - Expected: usize_to_i64(0) equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("is identity operation")
step("Verify: is identity operation")
expect(usize_to_i64(42)).to_equal(42)  # oracle: 42 — named expected value from the requirement
expect(usize_to_i64(0)).to_equal(0)  # oracle: 0 — named expected value from the requirement
```

</details>

### to_bool

#### recognizes truthy strings

- recognizes truthy strings
- Verify: recognizes truthy strings
   - Expected: to_bool("true") is true
   - Expected: to_bool("1") is true
   - Expected: to_bool("yes") is true
   - Expected: to_bool("on") is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("recognizes truthy strings")
step("Verify: recognizes truthy strings")
expect(to_bool("true")).to_equal(true)
expect(to_bool("1")).to_equal(true)
expect(to_bool("yes")).to_equal(true)
expect(to_bool("on")).to_equal(true)
```

</details>

#### is case-insensitive

- is case-insensitive
- Verify: is case-insensitive
   - Expected: to_bool("TRUE") is true
   - Expected: to_bool("Yes") is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("is case-insensitive")
step("Verify: is case-insensitive")
expect(to_bool("TRUE")).to_equal(true)
expect(to_bool("Yes")).to_equal(true)
```

</details>

#### returns false for other strings

- returns false for other strings
- Verify: returns false for other strings
   - Expected: to_bool("false") is false
   - Expected: to_bool("no") is false
   - Expected: to_bool("") is false
   - Expected: to_bool("random") is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns false for other strings")
step("Verify: returns false for other strings")
expect(to_bool("false")).to_equal(false)
expect(to_bool("no")).to_equal(false)
expect(to_bool("")).to_equal(false)
expect(to_bool("random")).to_equal(false)
```

</details>

### bool_to_text

#### converts true to text

- converts true to text
- Verify: converts true to text
   - Expected: bool_to_text(true) equals `true`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("converts true to text")
step("Verify: converts true to text")
expect(bool_to_text(true)).to_equal("true")
```

</details>

#### converts false to text

- converts false to text
- Verify: converts false to text
   - Expected: bool_to_text(false) equals `false`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("converts false to text")
step("Verify: converts false to text")
expect(bool_to_text(false)).to_equal("false")
```

</details>

### i64_to_text

#### converts integers to text

- converts integers to text
- Verify: converts integers to text
   - Expected: i64_to_text(42) equals `42`
   - Expected: i64_to_text(0) equals `0`
   - Expected: i64_to_text(-1) equals `-1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("converts integers to text")
step("Verify: converts integers to text")
expect(i64_to_text(42)).to_equal("42")
expect(i64_to_text(0)).to_equal("0")
expect(i64_to_text(-1)).to_equal("-1")
```

</details>

### f64_to_text

#### converts floats to text

- converts floats to text
- Verify: converts floats to text


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("converts floats to text")
step("Verify: converts floats to text")
val result = f64_to_text(3.14)
expect(result).to_contain("3.14")
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 22 |
| Active scenarios | 22 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-UNIT`
- `REQ-LIB-COMMON-001`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `508e4755e73ce74e833b7ebe40d24095d2cbb2bdcd6c19583f5ba9597258b77a`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `508e4755e73ce74e833b7ebe40d24095d2cbb2bdcd6c19583f5ba9597258b77a`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `508e4755e73ce74e833b7ebe40d24095d2cbb2bdcd6c19583f5ba9597258b77a`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **86/100**; effective score: **86/100**; blockers: **0**.

SSpec documentization score: 86/100
source: test/unit/lib/common/convert_spec.spl
mirror: doc/06_spec/unit/lib/common/convert_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/unit/lib/common/convert_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/unit/lib/common/convert_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: scope, assumptions/preconditions, primary workflow, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/unit/lib/common/convert_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 26 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/unit/lib/common/convert_spec.spl:24:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'returns value for digits 0-9' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/lib/common/convert_spec.spl:33:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'returns -1 for non-digits' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/lib/common/convert_spec.spl:42:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'parses positive integers' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
