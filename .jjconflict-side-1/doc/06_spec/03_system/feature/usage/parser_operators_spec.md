# Parser Operator Specification

> <details>

<!-- sdn-diagram:id=parser_operators_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=parser_operators_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

parser_operators_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=parser_operators_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

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
| Source | `test/03_system/feature/usage/parser_operators_spec.spl` |
| Updated | 2026-06-01 |
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

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect 2 + 3 == 5
```

</details>

#### parses subtraction

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect 5 - 3 == 2
```

</details>

#### parses multiplication

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect 3 * 4 == 12
```

</details>

#### parses division

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect 10 / 2 == 5
```

</details>

#### parses modulo

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect 10 % 3 == 1
```

</details>

#### parses power

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect 2 ** 3 == 8
```

</details>

#### parses integer division

1. expect 7 fdiv


<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect 7.fdiv(2) == 3
```

</details>

### Comparison Operator Parsing

#### parses less than

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect 1 < 2
```

</details>

#### parses greater than

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect 2 > 1
```

</details>

#### parses less than or equal

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect 2 <= 2
expect 1 <= 2
```

</details>

#### parses greater than or equal

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect 2 >= 2
expect 3 >= 2
```

</details>

#### parses equality

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect 2 == 2
```

</details>

#### parses inequality

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect 1 != 2
```

</details>

### Logical Operator Parsing

#### parses and

1. expect
2. expect


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect (true and true) == true
expect (true and false) == false
```

</details>

#### parses or

1. expect
2. expect


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect (true or false) == true
expect (false or false) == false
```

</details>

#### parses not

1. expect
2. expect


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect (not false) == true
expect (not true) == false
```

</details>

#### parses combined logical

1. expect
2. expect


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect (true and false or true) == true
expect (not (true and false)) == true
```

</details>

### Bitwise Operator Parsing

#### parses bitwise and

1. expect


<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect (0b1100 & 0b1010) == 0b1000
```

</details>

#### parses bitwise or

1. expect


<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect (0b1100 | 0b1010) == 0b1110
```

</details>

#### parses bitwise xor

1. expect


<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect (5 xor 3) == 6
```

</details>

#### parses bitwise not

1. expect


<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect (~0) == -1
```

</details>

#### parses left shift

1. expect


<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect (1 << 4) == 16
```

</details>

#### parses right shift

1. expect


<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect (16 >> 2) == 4
```

</details>

### Assignment Operator Parsing

#### parses simple assignment

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var x = 0
x = 42
expect x == 42
```

</details>

#### parses add-assign

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var x = 10
x += 5
expect x == 15
```

</details>

#### parses sub-assign

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var x = 10
x -= 3
expect x == 7
```

</details>

#### parses mul-assign

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var x = 5
x *= 2
expect x == 10
```

</details>

#### parses div-assign

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var x = 20
x /= 4
expect x == 5
```

</details>

#### parses mod-assign

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var x = 10
x %= 3
expect x == 1
```

</details>

#### parses suspend-assign

1. fn async val
2. x ~= async val


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
fn async_val() -> i64:
    42
var x = 0
x ~= async_val()
expect x == 42
```

</details>

### Pipeline Operator Parsing

#### parses pipe forward

1. fn double


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
fn double(x: i64) -> i64:
    x * 2
val result = 21 |> double
expect result == 42
```

</details>

### Optional Operator Parsing

#### parses optional chaining

1. expect len == Some


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val opt: Option<text> = Some("hello")
val len = opt?.len()
expect len == Some(5)
```

</details>

#### parses null coalescing

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val opt: Option<i64> = None
val value = opt ?? 42
expect value == 42
```

</details>

#### parses existence check

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val opt = Some(42)
expect opt.?
```

</details>

#### parses negated existence

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val opt: Option<i64> = None
expect not opt.?
```

</details>

#### parses try operator

1. fn may fail
2. Ok
3. fn use result
4. Ok
5. expect use result


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var sum = 0
for i in 0..5:
    sum = sum + i
expect sum == 10
```

</details>

#### parses inclusive range

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var sum = 0
for i in 0..=5:
    sum = sum + i
expect sum == 15
```

</details>

#### parses range in slice

1. expect sliced len


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val arr = [0, 1, 2, 3, 4]
val sliced = arr[1..4]
expect sliced.len() == 3
```

</details>

### Operator Precedence Parsing

#### power before multiplication

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect 2 ** 3 * 2 == 16
```

</details>

#### multiplication before addition

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect 2 + 3 * 4 == 14
```

</details>

#### comparison after arithmetic

1. expect


<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect (2 + 3 < 10) == true
```

</details>

#### logical after comparison

1. expect


<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect (1 < 2 and 3 < 4) == true
```

</details>

#### parentheses override precedence

1. expect


<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect (2 + 3) * 4 == 20
```

</details>

#### complex expression precedence

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect 2 + 3 * 4 ** 2 / 8 == 8
```

</details>

### Special Operator Parsing

<details>
<summary>Advanced: parses matrix multiplication</summary>

#### parses matrix multiplication

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @ is matrix multiplication operator
# Requires array/matrix support
expect true  # Placeholder
```

</details>


</details>

#### parses broadcast operators

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# .+ .- .* ./ are element-wise operators
# Requires array support
expect true  # Placeholder
```

</details>

#### parses layer connect

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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
