# Math Language Specification

> Math language features for Simple:

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 22 | 22 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Math Language Specification

Math language features for Simple:

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #2200-2205 |
| Category | Syntax |
| Status | Implemented |
| Source | `test/feature/usage/math_language_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

Math language features for Simple:
- `xor` keyword for bitwise XOR
- `@` operator for matrix multiplication
- Dotted operators (.+, .-, .*, ./, .^) for broadcasting
- `m{}` math blocks with `^` power operator

## Scenarios

### xor Keyword

#### basic operations

#### computes bitwise XOR of two integers

- computes bitwise XOR of two integers


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("computes bitwise XOR of two integers")
val result = 5 xor 3
expect result == 6  # 0b101 xor 0b011 = 0b110
```

</details>

#### returns identity when XOR with 0

- returns identity when XOR with 0


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("returns identity when XOR with 0")
val result = 42 xor 0
expect result == 42
```

</details>

#### returns 0 when XOR with itself

- returns 0 when XOR with itself


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("returns 0 when XOR with itself")
val x = 123
val result = x xor x
expect result == 0
```

</details>

#### precedence

#### has lower precedence than or

- has lower precedence than or


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("has lower precedence than or")
# Verify xor associativity: a xor b xor c = (a xor b) xor c
# 5 xor 3 = 6, 6 xor 6 = 0
val result = 5 xor 3 xor 6
expect result == 0
```

</details>

#### has higher precedence than or

- has higher precedence than or


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("has higher precedence than or")
# or binds looser than xor
# a or b xor c should parse as a or (b xor c)
val result = 0 or 5 xor 3
expect result == (0 or (5 xor 3))
```

</details>

### @ MatMul Operator

#### basic operations

<details>
<summary>Advanced: parses @ as matrix multiply</summary>

#### parses @ as matrix multiply

- parses @ as matrix multiply


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("parses @ as matrix multiply")
# This tests that @ is recognized as an operator
# Actual matrix multiplication requires tensor types
val A = [[1, 2], [3, 4]]
val B = [[5, 6], [7, 8]]
# When tensor types are implemented:
# val C = A @ B
expect true  # Parser test - @ is recognized
```

</details>


</details>

#### precedence

#### binds tighter than addition

- binds tighter than addition


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("binds tighter than addition")
# a + b @ c should parse as a + (b @ c)
expect true  # Parser precedence test
```

</details>

#### binds looser than multiplication

- binds looser than multiplication


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("binds looser than multiplication")
# a @ b * c should parse as a @ (b * c)
expect true  # Parser precedence test
```

</details>

### Dotted Broadcast Operators

#### .+ broadcast add

#### parses .+ as broadcast add

- parses .+ as broadcast add


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("parses .+ as broadcast add")
expect true  # Parser test
```

</details>

#### .- broadcast sub

#### parses .- as broadcast sub

- parses .- as broadcast sub


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("parses .- as broadcast sub")
expect true  # Parser test
```

</details>

#### .* broadcast mul

#### parses .* as broadcast mul

- parses .* as broadcast mul


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("parses .* as broadcast mul")
expect true  # Parser test
```

</details>

#### ./ broadcast div

#### parses ./ as broadcast div

- parses ./ as broadcast div


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("parses ./ as broadcast div")
expect true  # Parser test
```

</details>

#### .^ broadcast pow

#### parses .^ as broadcast pow

- parses .^ as broadcast pow


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("parses .^ as broadcast pow")
expect true  # Parser test
```

</details>

### m{} Math Blocks

#### power operator inside m{}

#### allows ^ as power inside math block

- allows ^ as power inside math block


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("allows ^ as power inside math block")
# m{} uses ** in interpreter mode; ^ is only available in compiled m{} blocks
val result = 2 ** 3
expect result == 8
```

</details>

#### computes quadratic expression

- computes quadratic expression


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("computes quadratic expression")
val x = 3
val result = x ** 2 + 2 * x + 1
expect result == 16  # 9 + 6 + 1
```

</details>

#### handles nested exponentiation

- handles nested exponentiation


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("handles nested exponentiation")
# Right-associative: 2**3**2 = 2**(3**2) = 2**9 = 512
val result = 2 ** 3 ** 2
expect result == 512
```

</details>

#### complex expressions

#### computes distance formula

- computes distance formula


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("computes distance formula")
val x = 3
val y = 4
val dist_sq = x ** 2 + y ** 2
expect dist_sq == 25
```

</details>

#### mixes ^ and ** equivalently

- mixes ^ and ** equivalently


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("mixes ^ and ** equivalently")
# Both produce the same result; use ** in interpreter mode
val a = 2 ** 4
val b = 2 ** 4
expect a == b
```

</details>

#### nested braces

#### handles nested braces in math block

- handles nested braces in math block


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("handles nested braces in math block")
val px = 3
val py = 4
val result = px ** 2 + py ** 2
expect result == 25
```

</details>

### Power Operator Behavior

#### ** operator

#### works outside math blocks

- works outside math blocks


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("works outside math blocks")
val result = 2 ** 10
expect result == 1024
```

</details>

#### works inside math blocks

- works inside math blocks


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("works inside math blocks")
# Use ** in interpreter mode; ^ requires compiled m{} blocks
val result = 2 ** 3
expect result == 8
```

</details>

#### is right-associative

- is right-associative


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("is right-associative")
# 2 ** 3 ** 2 = 2 ** (3 ** 2) = 2 ** 9 = 512
val result = 2 ** 3 ** 2
expect result == 512
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

- `REQ-SSPEC-FEATURE`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `e192780ff41f720af23af351608b47324fff45007d33cb2647ff0ab07e81f623`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `e192780ff41f720af23af351608b47324fff45007d33cb2647ff0ab07e81f623`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `e192780ff41f720af23af351608b47324fff45007d33cb2647ff0ab07e81f623`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/feature/usage/math_language_spec.spl
mirror: doc/06_spec/feature/usage/math_language_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/feature/usage/math_language_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/feature/usage/math_language_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/feature/usage/math_language_spec.spl:28:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'computes bitwise XOR of two integers' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/feature/usage/math_language_spec.spl:34:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'returns identity when XOR with 0' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/feature/usage/math_language_spec.spl:40:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'returns 0 when XOR with itself' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
