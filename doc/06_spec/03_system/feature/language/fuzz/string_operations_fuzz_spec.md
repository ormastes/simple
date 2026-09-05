# String Operations Fuzz Specification

> 1. lcg seed

<!-- sdn-diagram:id=string_operations_fuzz_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=string_operations_fuzz_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

string_operations_fuzz_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=string_operations_fuzz_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 11 | 11 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# String Operations Fuzz Specification

## Scenarios

### fuzz: string operations

#### string length is always non-negative

1. lcg seed
   - Expected: failures equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
lcg_seed(10001)
var failures = 0
for i in 0..100:
    val len = lcg_range(0, 50)
    val s = build_string("a", len)
    if s.len() < 0:
        failures = failures + 1
expect(failures).to_equal(0)
```

</details>

#### string length matches constructed length

1. lcg seed
   - Expected: failures equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
lcg_seed(10002)
var failures = 0
for i in 0..100:
    val len = lcg_range(0, 30)
    val s = build_string("x", len)
    if s.len() != len:
        failures = failures + 1
expect(failures).to_equal(0)
```

</details>

#### slicing with valid bounds works

1. lcg seed
   - Expected: failures equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
lcg_seed(10003)
var failures = 0
for i in 0..100:
    val len = lcg_range(2, 20)
    val s = build_string("m", len)
    val start = lcg_range(0, len - 1)
    val end = lcg_range(start + 1, len)
    val sliced = s[start:end]
    val expected_len = end - start
    if sliced.len() != expected_len:
        failures = failures + 1
expect(failures).to_equal(0)
```

</details>

#### contains finds substring that was appended

1. lcg seed
   - Expected: failures equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
lcg_seed(10004)
var failures = 0
for i in 0..50:
    val base = build_random_string(lcg_range(3, 10))
    val needle = build_random_string(lcg_range(1, 3))
    val combined = base + needle
    if combined.contains(needle) != true:
        failures = failures + 1
expect(failures).to_equal(0)
```

</details>

#### empty string concatenation is identity

1. lcg seed
   - Expected: failures equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
lcg_seed(10005)
var failures = 0
for i in 0..100:
    val s = build_random_string(lcg_range(0, 20))
    val with_empty = s + ""
    val empty_with = "" + s
    if with_empty != s:
        failures = failures + 1
    if empty_with != s:
        failures = failures + 1
expect(failures).to_equal(0)
```

</details>

#### empty string has length zero

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val s = ""
expect(s.len()).to_equal(0)
```

</details>

#### replace preserves length when replacement has same length

1. lcg seed
2. var replaced = s replace
   - Expected: failures equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
lcg_seed(10006)
var failures = 0
for i in 0..50:
    val len = lcg_range(5, 20)
    val s = build_string("a", len)
    # Replace single char with single char
    var replaced = s.replace("a", "b")
    if replaced.len() != s.len():
        failures = failures + 1
expect(failures).to_equal(0)
```

</details>

#### contains returns false for longer needle than haystack

1. lcg seed
   - Expected: failures equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
lcg_seed(10007)
var failures = 0
for i in 0..50:
    val short_len = lcg_range(1, 5)
    val long_len = lcg_range(6, 15)
    val haystack = build_string("z", short_len)
    val needle = build_string("a", long_len)
    if haystack.contains(needle) != false:
        failures = failures + 1
expect(failures).to_equal(0)
```

</details>

#### string equality is reflexive

1. lcg seed
   - Expected: failures equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
lcg_seed(10008)
var failures = 0
for i in 0..100:
    val s = build_random_string(lcg_range(0, 30))
    if s != s:
        failures = failures + 1
expect(failures).to_equal(0)
```

</details>

#### starts_with works for prefix of constructed string

1. lcg seed
   - Expected: failures equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
lcg_seed(10009)
var failures = 0
for i in 0..50:
    val prefix = build_random_string(lcg_range(1, 5))
    val suffix = build_random_string(lcg_range(1, 10))
    val combined = prefix + suffix
    if combined.starts_with(prefix) != true:
        failures = failures + 1
expect(failures).to_equal(0)
```

</details>

#### ends_with works for suffix of constructed string

1. lcg seed
   - Expected: failures equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
lcg_seed(10010)
var failures = 0
for i in 0..50:
    val prefix = build_random_string(lcg_range(1, 5))
    val suffix = build_random_string(lcg_range(1, 10))
    val combined = prefix + suffix
    if combined.ends_with(suffix) != true:
        failures = failures + 1
expect(failures).to_equal(0)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/03_system/feature/language/fuzz/string_operations_fuzz_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- fuzz: string operations

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 11 |
| Active scenarios | 11 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
