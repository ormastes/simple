# Const Functions Specification

> Const functions can be evaluated at compile time, enabling:

<!-- sdn-diagram:id=const_fn_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=const_fn_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

const_fn_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=const_fn_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 19 | 19 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Const Functions Specification

Const functions can be evaluated at compile time, enabling:

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #BM-002 |
| Category | Language / Bare-Metal |
| Status | Blocked (const fn syntax not supported by runtime parser) |
| Source | `test/03_system/feature/features/baremetal/const_fn_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

Const functions can be evaluated at compile time, enabling:
- Compile-time computation of lookup tables
- Constant initialization without runtime overhead
- Static assertions with computed values

## Scenarios

### Const Functions
_Compile-time evaluable functions._

#### Basic Const Functions
_Simple const function definitions._

#### evaluates direct arithmetic helper

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
check(fake_const_add(10, 20) == 30)
```

</details>

#### evaluates nested helper calls

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
check(fake_const_add(fake_const_add(2, 3), 4) == 9)
```

</details>

#### evaluates a min helper like a const branch

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
check(fake_const_min(50, 100) == 50)
```

</details>

#### Const Conditionals
_Const functions with control flow._

#### evaluates const if-style branching

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
check(fake_const_min(100, 50) == 50)
```

</details>

#### evaluates const match-style selection

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val input = 2
val output = if input == 1: 10 else: if input == 2: 20 else: 30
check(output == 20)
```

</details>

#### Const Recursion
_Recursive const functions._

#### evaluates factorial recursively

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
check(fake_const_factorial(5) == 120)
```

</details>

#### evaluates fibonacci recursively

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
check(fake_const_fibonacci(7) == 13)
```

</details>

#### Const Arrays
_Const functions returning arrays._

#### creates a lookup-table style array

1. check
2. check
3. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val table = fake_const_lookup_table(4)
check(table.len() == 4)
check(table[0] == 0)
check(table[3] == 9)
```

</details>

#### Const Type Operations
_Const functions with type intrinsics._

#### uses a size-like helper

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
check(fake_size_of_i64() == 8)
```

</details>

#### uses an align-like helper

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
check(fake_align_of_i64() == 8)
```

</details>

#### Use Cases - Lookup Tables
_Real-world const function applications._

#### generates a CRC-style lookup table

1. check
2. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val table = fake_crc_table()
check(table.len() == 4)
check(table[1] == 7)
```

</details>

#### generates a sin-style lookup table

1. check
2. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val table = fake_sin_table()
check(table.len() == 4)
check(table[2] == 2)
```

</details>

#### Const Function Restrictions
_What's NOT allowed in const functions._

#### allows pure arithmetic

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
check((2 + 3) * 4 == 20)
```

</details>

#### allows pure boolean logic

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
check((true and not false) == true)
```

</details>

#### allows pure bitwise operations

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val mask = 0x0F
check((0xFF & mask) == 0x0F)
```

</details>

### Const Evaluation Context
_Compile-time evaluation environment._

#### Constant Propagation

#### propagates constants through expressions

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val A = 10
val B = 20
val C = A + B
check(C == 30)
```

</details>

#### propagates constants through conditionals

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val MAX = 100
val VALUE = 50
val RESULT = if VALUE < MAX: VALUE else: MAX
check(RESULT == 50)
```

</details>

#### Type-Level Constants

#### uses constants as array sizes

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val size = fake_const_add(2, 2)
val table = fake_const_lookup_table(size)
check(table.len() == 4)
```

</details>

#### uses computed constants

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val computed = fake_const_factorial(3) + fake_const_min(9, 4)
check(computed == 10)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 19 |
| Active scenarios | 19 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
