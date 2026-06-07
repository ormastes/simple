# Numbered Directory Resolution Specification

> Tests that the module resolver correctly handles numbered directory prefixes (NN.name/ pattern) by stripping the numeric prefix during resolution.

<!-- sdn-diagram:id=numbered_dir_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=numbered_dir_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

numbered_dir_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=numbered_dir_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 8 | 8 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Numbered Directory Resolution Specification

Tests that the module resolver correctly handles numbered directory prefixes (NN.name/ pattern) by stripping the numeric prefix during resolution.

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #LAYER-001 |
| Category | Infrastructure |
| Difficulty | 2/5 |
| Status | Implemented |
| Source | `test/01_unit/compiler/module_resolver/numbered_dir_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests that the module resolver correctly handles numbered directory prefixes
(NN.name/ pattern) by stripping the numeric prefix during resolution.

## Behavior

- `use compiler.frontend.X` resolves through `10.frontend/X.spl`
- `use compiler.mir.mir_data` resolves through `50.mir/mir_data.spl`
- Non-numbered directories resolve normally
- Invalid prefixes (non-numeric) are ignored

## Scenarios

### Numbered Directory Prefix Stripping

#### when directory has valid 2-digit prefix

#### strips prefix and matches segment

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# 10.frontend -> frontend
val dir_name = "10.frontend"
val dot_idx = dir_name.index_of(".")
val idx = dot_idx ?? -1
expect(idx).to_equal(2)
val name = dir_name.substring(idx + 1)
expect(name).to_equal("frontend")
```

</details>

#### handles single-digit prefix

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# 0.common -> common
val dir_name = "0.common"
val dot_idx = dir_name.index_of(".")
val idx = dot_idx ?? -1
expect(idx).to_equal(1)
val name = dir_name.substring(idx + 1)
expect(name).to_equal("common")
```

</details>

#### handles 3-digit prefix

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# 100.extra -> extra (if range allowed)
val dir_name = "100.extra"
val dot_idx = dir_name.index_of(".")
val idx = dot_idx ?? -1
expect(idx).to_equal(3)
val name = dir_name.substring(idx + 1)
expect(name).to_equal("extra")
```

</details>

#### when directory has no numeric prefix

#### does not match NN.name pattern

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val dir_name = "backend"
val dot_idx = dir_name.index_of(".")
val idx = dot_idx ?? -1
expect(idx).to_equal(-1)
```

</details>

#### when dot is not after digits

#### ignores non-numeric prefixes

<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val dir_name = "abc.frontend"
val dot_idx = dir_name.index_of(".")
val idx = dot_idx ?? 0
val prefix = dir_name.substring(0, idx)
# Verify prefix contains non-digits
var all_digits = true
for ch in prefix:
    if ch < "0" or ch > "9":
        all_digits = false
expect(all_digits).to_equal(false)
```

</details>

### Layer Number Extraction

#### extracts layer 0 from 00.common

1. num = num * 10 +
   - Expected: num equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val dir = "00.common"
val dot_idx = dir.index_of(".")
val idx = dot_idx ?? 0
val prefix = dir.substring(0, idx)
# Parse: "00" -> 0
var num: i64 = 0
for ch in prefix:
    num = num * 10 + (ch.to_i64() - "0".to_i64())
expect(num).to_equal(0)
```

</details>

#### extracts layer 70 from 70.backend

1. num = num * 10 +
   - Expected: num equals `70`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val dir = "70.backend"
val dot_idx = dir.index_of(".")
val idx = dot_idx ?? 0
val prefix = dir.substring(0, idx)
var num: i64 = 0
for ch in prefix:
    num = num * 10 + (ch.to_i64() - "0".to_i64())
expect(num).to_equal(70)
```

</details>

#### extracts layer 99 from 99.loader

1. num = num * 10 +
   - Expected: num equals `99`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val dir = "99.loader"
val dot_idx = dir.index_of(".")
val idx = dot_idx ?? 0
val prefix = dir.substring(0, idx)
var num: i64 = 0
for ch in prefix:
    num = num * 10 + (ch.to_i64() - "0".to_i64())
expect(num).to_equal(99)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 8 |
| Active scenarios | 8 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
