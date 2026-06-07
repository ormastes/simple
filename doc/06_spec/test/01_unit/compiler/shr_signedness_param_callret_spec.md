# Shr Signedness Param Callret Specification

> <details>

<!-- sdn-diagram:id=shr_signedness_param_callret_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=shr_signedness_param_callret_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

shr_signedness_param_callret_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=shr_signedness_param_callret_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 4 | 4 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Shr Signedness Param Callret Specification

## Scenarios

### right-shift signedness — param + call-return paths

#### signed param: shr_signed_param(-16) yields -8

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val got: i32 = shr_signed_param(-16)
expect(got).to_equal(-8)
```

</details>

#### unsigned param: shr_unsigned_param(2147483648) yields 1073741824

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val got: u32 = shr_unsigned_param(2147483648 as u32)
val expected: u32 = 1073741824 as u32
expect(got).to_equal(expected)
```

</details>

#### signed call-return: get_neg_sixteen() >> 1 yields -8

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val v: i32 = get_neg_sixteen()
val got: i32 = v >> 1
expect(got).to_equal(-8)
```

</details>

#### unsigned call-return: get_high_bit() >> 1 yields 1073741824

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val v: u32 = get_high_bit()
val got: u32 = v >> 1
val expected: u32 = 1073741824 as u32
expect(got).to_equal(expected)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler/shr_signedness_param_callret_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- right-shift signedness — param + call-return paths

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 4 |
| Active scenarios | 4 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
