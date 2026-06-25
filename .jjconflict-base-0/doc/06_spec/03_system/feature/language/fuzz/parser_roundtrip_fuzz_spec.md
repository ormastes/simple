# Parser Roundtrip Fuzz Specification

> 1. lcg seed

<!-- sdn-diagram:id=parser_roundtrip_fuzz_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=parser_roundtrip_fuzz_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

parser_roundtrip_fuzz_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=parser_roundtrip_fuzz_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 10 | 10 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Parser Roundtrip Fuzz Specification

## Scenarios

### fuzz: parser roundtrip

#### integer literals are stable through to_text/int conversion

1. lcg seed
   - Expected: failures equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
lcg_seed(12345)
var failures = 0
for i in 0..200:
    val n = lcg_range(-5000, 5000)
    val s = "{n}"
    val back = int(s)
    if back != n:
        failures = failures + 1
expect(failures).to_equal(0)
```

</details>

#### string concatenation is associative

1. lcg seed
   - Expected: failures equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
lcg_seed(67890)
var failures = 0
for i in 0..100:
    val a_num = lcg_range(0, 100)
    val b_num = lcg_range(0, 100)
    val c_num = lcg_range(0, 100)
    val a = "s_{a_num}"
    val b = "s_{b_num}"
    val c = "s_{c_num}"
    val ab_c = a + b + c
    val a_bc = a + (b + c)
    if ab_c != a_bc:
        failures = failures + 1
expect(failures).to_equal(0)
```

</details>

#### integer negation is involutory

1. lcg seed
   - Expected: failures equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
lcg_seed(11111)
var failures = 0
for i in 0..200:
    val n = lcg_range(-10000, 10000)
    val neg_neg = -(-n)
    if neg_neg != n:
        failures = failures + 1
expect(failures).to_equal(0)
```

</details>

#### string length matches content after interpolation

1. lcg seed
   - Expected: failures equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
lcg_seed(22222)
var failures = 0
for i in 0..100:
    val x = lcg_range(0, 1000)
    val s = "{x}"
    val expected_len = "{x}".len()
    if s.len() != expected_len:
        failures = failures + 1
expect(failures).to_equal(0)
```

</details>

#### repeated string building is consistent

1. lcg seed
   - Expected: failures equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
lcg_seed(33333)
var failures = 0
for i in 0..50:
    val count = lcg_range(1, 10)
    var built1 = ""
    var built2 = ""
    for j in 0..count:
        built1 = built1 + "x"
        built2 = built2 + "x"
    if built1 != built2:
        failures = failures + 1
expect(failures).to_equal(0)
```

</details>

#### integer to text roundtrip preserves sign

1. lcg seed
   - Expected: failures equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
lcg_seed(44444)
var failures = 0
for i in 0..200:
    val n = lcg_range(-9999, 9999)
    val s = "{n}"
    val back = int(s)
    val sign_original = if n < 0: -1 else: if n > 0: 1 else: 0
    val sign_back = if back < 0: -1 else: if back > 0: 1 else: 0
    if sign_original != sign_back:
        failures = failures + 1
expect(failures).to_equal(0)
```

</details>

#### addition is commutative across random pairs

1. lcg seed
   - Expected: failures equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
lcg_seed(55555)
var failures = 0
for i in 0..200:
    val a = lcg_range(-10000, 10000)
    val b = lcg_range(-10000, 10000)
    if a + b != b + a:
        failures = failures + 1
expect(failures).to_equal(0)
```

</details>

#### multiplication is commutative across random pairs

1. lcg seed
   - Expected: failures equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
lcg_seed(66666)
var failures = 0
for i in 0..200:
    val a = lcg_range(-1000, 1000)
    val b = lcg_range(-1000, 1000)
    if a * b != b * a:
        failures = failures + 1
expect(failures).to_equal(0)
```

</details>

#### string repeat length is predictable

1. lcg seed
   - Expected: failures equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
lcg_seed(77777)
var failures = 0
for i in 0..50:
    val count = lcg_range(0, 20)
    var s = ""
    for j in 0..count:
        s = s + "ab"
    if s.len() != count * 2:
        failures = failures + 1
expect(failures).to_equal(0)
```

</details>

#### zero is additive identity for random numbers

1. lcg seed
   - Expected: failures equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
lcg_seed(88888)
var failures = 0
for i in 0..200:
    val n = lcg_range(-100000, 100000)
    if n + 0 != n:
        failures = failures + 1
    if 0 + n != n:
        failures = failures + 1
expect(failures).to_equal(0)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/03_system/feature/language/fuzz/parser_roundtrip_fuzz_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- fuzz: parser roundtrip

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 10 |
| Active scenarios | 10 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
