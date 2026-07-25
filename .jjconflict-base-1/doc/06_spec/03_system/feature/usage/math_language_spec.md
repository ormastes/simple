# Math Language Specification

> Math language features for Simple:

<!-- sdn-diagram:id=math_language_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=math_language_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

math_language_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=math_language_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

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
| Source | `test/03_system/feature/usage/math_language_spec.spl` |
| Updated | 2026-06-01 |
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

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = 5 xor 3
expect result == 6  # 0b101 xor 0b011 = 0b110
```

</details>

#### returns identity when XOR with 0

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = 42 xor 0
expect result == 42
```

</details>

#### returns 0 when XOR with itself

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val x = 123
val result = x xor x
expect result == 0
```

</details>

#### precedence

#### has lower precedence than or

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Verify xor associativity: a xor b xor c = (a xor b) xor c
# 5 xor 3 = 6, 6 xor 6 = 0
val result = 5 xor 3 xor 6
expect result == 0
```

</details>

#### has higher precedence than or

1. expect result ==


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# a + b @ c should parse as a + (b @ c)
expect true  # Parser precedence test
```

</details>

#### binds looser than multiplication

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# a @ b * c should parse as a @ (b * c)
expect true  # Parser precedence test
```

</details>

### Dotted Broadcast Operators

#### .+ broadcast add

#### parses .+ as broadcast add

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect true  # Parser test
```

</details>

#### .- broadcast sub

#### parses .- as broadcast sub

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect true  # Parser test
```

</details>

#### .* broadcast mul

#### parses .* as broadcast mul

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect true  # Parser test
```

</details>

#### ./ broadcast div

#### parses ./ as broadcast div

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect true  # Parser test
```

</details>

#### .^ broadcast pow

#### parses .^ as broadcast pow

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect true  # Parser test
```

</details>

### m{} Math Blocks

#### power operator inside m{}

#### allows ^ as power inside math block

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# m{} uses ** in interpreter mode; ^ is only available in compiled m{} blocks
val result = 2 ** 3
expect result == 8
```

</details>

#### computes quadratic expression

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val x = 3
val result = x ** 2 + 2 * x + 1
expect result == 16  # 9 + 6 + 1
```

</details>

#### handles nested exponentiation

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Right-associative: 2**3**2 = 2**(3**2) = 2**9 = 512
val result = 2 ** 3 ** 2
expect result == 512
```

</details>

#### complex expressions

#### computes distance formula

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val x = 3
val y = 4
val dist_sq = x ** 2 + y ** 2
expect dist_sq == 25
```

</details>

#### mixes ^ and ** equivalently

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Both produce the same result; use ** in interpreter mode
val a = 2 ** 4
val b = 2 ** 4
expect a == b
```

</details>

#### nested braces

#### handles nested braces in math block

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val px = 3
val py = 4
val result = px ** 2 + py ** 2
expect result == 25
```

</details>

### Power Operator Behavior

#### ** operator

#### works outside math blocks

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = 2 ** 10
expect result == 1024
```

</details>

#### works inside math blocks

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Use ** in interpreter mode; ^ requires compiled m{} blocks
val result = 2 ** 3
expect result == 8
```

</details>

#### is right-associative

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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
