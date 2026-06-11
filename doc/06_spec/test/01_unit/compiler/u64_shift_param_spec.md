# U64 Shift Param Specification

> 1. var result: u64 = shr u64

<!-- sdn-diagram:id=u64_shift_param_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=u64_shift_param_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

u64_shift_param_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=u64_shift_param_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 8 | 8 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# U64 Shift Param Specification

## Scenarios

### u64 right shift via fn param

#### logical shift high-bit value (unsuffixed hex)

1. var result: u64 = shr u64
   - Expected: result equals `0x4000000000000000u64`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# 0x8000000000000000 without u64 suffix parses as Value::Int(i64::MIN)
# coerce_unsigned must convert to UInt before shift
var result: u64 = shr_u64(0x8000000000000000)
expect(result).to_equal(0x4000000000000000u64)
```

</details>

#### logical shift all-ones (unsuffixed hex)

1. var result: u64 = shr u64
   - Expected: result equals `0x7FFFFFFFFFFFFFFFu64`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# 0xFFFFFFFFFFFFFFFF without u64 suffix parses as Value::Int(-1)
var result: u64 = shr_u64(0xFFFFFFFFFFFFFFFF)
expect(result).to_equal(0x7FFFFFFFFFFFFFFFu64)
```

</details>

#### logical shift SHA-384 initial hash value (unsuffixed)

1. var result: u64 = shr u64 by
   - Expected: result equals `0x0000000CBBB9D5DCu64`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# 0xCBBB9D5DC1059ED8 parses as negative Value::Int
# This is the exact repro from the bug doc
var result: u64 = shr_u64_by(0xCBBB9D5DC1059ED8, 28)
expect(result).to_equal(0x0000000CBBB9D5DCu64)
```

</details>

#### no sign extension on high-bit u64 param (unsuffixed)

1. var result: u64 = shr u64 by
   - Expected: result equals `0x4000000000000000u64`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var x: u64 = 0x8000000000000000
var result: u64 = shr_u64_by(x, 1)
expect(result).to_equal(0x4000000000000000u64)
```

</details>

### u64 right shift via overloaded fn (bind_args_with_values path)

#### overloaded: logical shift SHA-384 initial hash value

1. var result: u64 = shift right
   - Expected: result equals `0x0000000CBBB9D5DCu64`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# This exercises Priority 4 overload dispatch -> exec_function_with_values
# -> bind_args_with_values which was missing coerce_unsigned
# The overload resolver pre-evaluates args then calls bind_args_with_values
var result: u64 = shift_right(0xCBBB9D5DC1059ED8, 28)
expect(result).to_equal(0x0000000CBBB9D5DCu64)
```

</details>

#### overloaded: logical shift high-bit value

1. var result: u64 = shift right
   - Expected: result equals `0x4000000000000000u64`


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var result: u64 = shift_right(0x8000000000000000, 1)
expect(result).to_equal(0x4000000000000000u64)
```

</details>

#### overloaded: logical shift all-ones

1. var result: u64 = shift right
   - Expected: result equals `0x7FFFFFFFFFFFFFFFu64`


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var result: u64 = shift_right(0xFFFFFFFFFFFFFFFF, 1)
expect(result).to_equal(0x7FFFFFFFFFFFFFFFu64)
```

</details>

#### overloaded: no sign extension on high-bit variable

1. var result: u64 = shift right
   - Expected: result equals `0x4000000000000000u64`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var x: u64 = 0x8000000000000000
var result: u64 = shift_right(x, 1)
expect(result).to_equal(0x4000000000000000u64)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler/u64_shift_param_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- u64 right shift via fn param
- u64 right shift via overloaded fn (bind_args_with_values path)

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 8 |
| Active scenarios | 8 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
