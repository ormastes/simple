# Regex Utils Specification

> 1. expect regex is match

<!-- sdn-diagram:id=regex_utils_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=regex_utils_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

regex_utils_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=regex_utils_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 6 | 6 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Regex Utils Specification

## Scenarios

### Regex Utils

#### matches digit patterns

1. expect regex is match
2. expect regex is match


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect regex_is_match(r"\d+", "build 42 passed") == true
expect regex_is_match(r"^\d+$", "42x") == false
```

</details>

#### finds the first number with range metadata

1. Some


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val found = regex_find(r"\d+", "run 128 ms")
match found:
    Some(m):
        expect m.text == "128"
        expect m.start == 4
        expect m.end == 7
    nil:
        expect false
```

</details>

#### replaces all numeric runs

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val replaced = regex_replace_all(r"\d+", "p50=12 p95=48", "N")
expect replaced == "pN=N pN=N"
```

</details>

#### splits comma separated text and trims spacing

1. expect parts len


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val parts = regex_split(r",\s*", "alpha, beta,gamma")
expect parts.len() == 3
expect parts[1] == "beta"
```

</details>

#### validates common email and ipv4 shapes

1. expect is valid email
2. expect is valid email
3. expect is valid ipv4
4. expect is valid ipv4


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect is_valid_email("dev@example.com") == true
expect is_valid_email("@example.com") == false
expect is_valid_ipv4("192.168.0.1") == true
expect is_valid_ipv4("999.168.0.1") == false
```

</details>

#### extracts numeric strings in order

1. expect nums len


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val nums = extract_numbers("x=7 y=11 z=19")
expect nums.len() == 3
expect nums[0] == "7"
expect nums[2] == "19"
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/01_unit/app/tooling/regex_utils_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- Regex Utils

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 6 |
| Active scenarios | 6 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
