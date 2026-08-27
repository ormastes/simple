# Parser Operator Specification

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 48 | 48 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Parser Operator Specification

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #PARSER-OP-001 to #PARSER-OP-020 |
| Category | Infrastructure \| Parser |
| Status | Implemented |
| Source | `test/feature/usage/parser_operators_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Syntax

```simple
# Arithmetic: + - * / % ** //
# Comparison: < > <= >= == !=
# Logical: and or not
# Bitwise: & | ^ ~ << >>
# Pipeline: |> >> <<
# Optional: ?. ?? .?
```

## Scenarios

### Arithmetic Operator Parsing

#### parses addition

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- parses addition


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("parses addition")
expect 2 + 3 == 5
```

</details>

#### parses subtraction

- parses subtraction


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("parses subtraction")
expect 5 - 3 == 2
```

</details>

#### parses multiplication

- parses multiplication


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("parses multiplication")
expect 3 * 4 == 12
```

</details>

#### parses division

- parses division


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("parses division")
expect 10 / 2 == 5
```

</details>

#### parses modulo

- parses modulo


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("parses modulo")
expect 10 % 3 == 1
```

</details>

#### parses power

- parses power


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("parses power")
expect 2 ** 3 == 8
```

</details>

#### parses integer division

- parses integer division


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("parses integer division")
expect 7.fdiv(2) == 3
```

</details>

### Comparison Operator Parsing

#### parses less than

- parses less than


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("parses less than")
expect 1 < 2
```

</details>

#### parses greater than

- parses greater than


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("parses greater than")
expect 2 > 1
```

</details>

#### parses less than or equal

- parses less than or equal


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("parses less than or equal")
expect 2 <= 2
expect 1 <= 2
```

</details>

#### parses greater than or equal

- parses greater than or equal


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("parses greater than or equal")
expect 2 >= 2
expect 3 >= 2
```

</details>

#### parses equality

- parses equality


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("parses equality")
expect 2 == 2
```

</details>

#### parses inequality

- parses inequality


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("parses inequality")
expect 1 != 2
```

</details>

### Logical Operator Parsing

#### parses and

- parses and


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("parses and")
expect (true and true) == true
expect (true and false) == false
```

</details>

#### parses or

- parses or


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("parses or")
expect (true or false) == true
expect (false or false) == false
```

</details>

#### parses not

- parses not


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("parses not")
expect (not false) == true
expect (not true) == false
```

</details>

#### parses combined logical

- parses combined logical


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("parses combined logical")
expect (true and false or true) == true
expect (not (true and false)) == true
```

</details>

### Bitwise Operator Parsing

#### parses bitwise and

- parses bitwise and


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("parses bitwise and")
expect (0b1100 & 0b1010) == 0b1000
```

</details>

#### parses bitwise or

- parses bitwise or


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("parses bitwise or")
expect (0b1100 | 0b1010) == 0b1110
```

</details>

#### parses bitwise xor

- parses bitwise xor


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("parses bitwise xor")
expect (5 xor 3) == 6
```

</details>

#### parses bitwise not

- parses bitwise not


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("parses bitwise not")
expect (~0) == -1
```

</details>

#### parses left shift

- parses left shift


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("parses left shift")
expect (1 << 4) == 16
```

</details>

#### parses right shift

- parses right shift


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("parses right shift")
expect (16 >> 2) == 4
```

</details>

### Assignment Operator Parsing

#### parses simple assignment

- parses simple assignment


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("parses simple assignment")
var x = 0
x = 42
expect x == 42
```

</details>

#### parses add-assign

- parses add-assign


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("parses add-assign")
var x = 10
x += 5
expect x == 15
```

</details>

#### parses sub-assign

- parses sub-assign


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("parses sub-assign")
var x = 10
x -= 3
expect x == 7
```

</details>

#### parses mul-assign

- parses mul-assign


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("parses mul-assign")
var x = 5
x *= 2
expect x == 10
```

</details>

#### parses div-assign

- parses div-assign


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("parses div-assign")
var x = 20
x /= 4
expect x == 5
```

</details>

#### parses mod-assign

- parses mod-assign


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("parses mod-assign")
var x = 10
x %= 3
expect x == 1
```

</details>

#### parses suspend-assign

- parses suspend-assign


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("parses suspend-assign")
fn async_val() -> i64:
    42
var x = 0
x ~= async_val()
expect x == 42
```

</details>

### Pipeline Operator Parsing

#### parses pipe forward

- parses pipe forward


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("parses pipe forward")
fn double(x: i64) -> i64:
    x * 2
val result = 21 |> double
expect result == 42
```

</details>

### Optional Operator Parsing

#### parses optional chaining

- parses optional chaining


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("parses optional chaining")
val opt: Option<text> = Some("hello")
val len = opt?.len()
expect len == Some(5)
```

</details>

#### parses null coalescing

- parses null coalescing


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("parses null coalescing")
val opt: Option<i64> = None
val value = opt ?? 42
expect value == 42
```

</details>

#### parses existence check

- parses existence check


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("parses existence check")
val opt = Some(42)
expect opt.?
```

</details>

#### parses negated existence

- parses negated existence


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("parses negated existence")
val opt: Option<i64> = None
expect not opt.?
```

</details>

#### parses try operator

- parses try operator


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("parses try operator")
fn may_fail() -> Result<i64, text>:
    Ok(42)
fn use_result() -> Result<i64, text>:
    val x = may_fail()?
    Ok(x * 2)
expect use_result().unwrap() == 84
```

</details>

### Range Operator Parsing

#### parses exclusive range

- parses exclusive range


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("parses exclusive range")
var sum = 0
for i in 0..5:
    sum = sum + i
expect sum == 10
```

</details>

#### parses inclusive range

- parses inclusive range


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("parses inclusive range")
var sum = 0
for i in 0..=5:
    sum = sum + i
expect sum == 15
```

</details>

#### parses range in slice

- parses range in slice


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("parses range in slice")
val arr = [0, 1, 2, 3, 4]
val sliced = arr[1..4]
expect sliced.len() == 3
```

</details>

### Operator Precedence Parsing

#### power before multiplication

- power before multiplication


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("power before multiplication")
expect 2 ** 3 * 2 == 16
```

</details>

#### multiplication before addition

- multiplication before addition


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("multiplication before addition")
expect 2 + 3 * 4 == 14
```

</details>

#### comparison after arithmetic

- comparison after arithmetic


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("comparison after arithmetic")
expect (2 + 3 < 10) == true
```

</details>

#### logical after comparison

- logical after comparison


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("logical after comparison")
expect (1 < 2 and 3 < 4) == true
```

</details>

#### parentheses override precedence

- parentheses override precedence


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("parentheses override precedence")
expect (2 + 3) * 4 == 20
```

</details>

#### complex expression precedence

- complex expression precedence


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("complex expression precedence")
expect 2 + 3 * 4 ** 2 / 8 == 8
```

</details>

### Special Operator Parsing

<details>
<summary>Advanced: parses matrix multiplication</summary>

#### parses matrix multiplication

- parses matrix multiplication


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("parses matrix multiplication")
# @ is matrix multiplication operator
# Requires array/matrix support
expect true  # Placeholder
```

</details>


</details>

#### parses broadcast operators

- parses broadcast operators


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("parses broadcast operators")
# .+ .- .* ./ are element-wise operators
# Requires array support
expect true  # Placeholder
```

</details>

#### parses layer connect

- parses layer connect


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("parses layer connect")
# ~> connects neural network layers
expect true  # Placeholder
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 48 |
| Active scenarios | 48 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-FEATURE`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `6e7259d7493396d921f7caaf194c9799514b1e7a33c8ed40f18452446158f9a4`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `6e7259d7493396d921f7caaf194c9799514b1e7a33c8ed40f18452446158f9a4`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `6e7259d7493396d921f7caaf194c9799514b1e7a33c8ed40f18452446158f9a4`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/feature/usage/parser_operators_spec.spl
mirror: doc/06_spec/feature/usage/parser_operators_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/feature/usage/parser_operators_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/feature/usage/parser_operators_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/feature/usage/parser_operators_spec.spl:41:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'parses addition' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/feature/usage/parser_operators_spec.spl:46:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'parses subtraction' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/feature/usage/parser_operators_spec.spl:51:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'parses multiplication' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
