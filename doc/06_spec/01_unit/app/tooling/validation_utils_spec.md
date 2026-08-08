# Validation Utilities Specification

> This specification covers basic validation utility functions for common data validation tasks: 1. Number range validation (positive, negative, in-range) 2. String validation (not empty) 3. Type-specific validation helpers 4. Common validation patterns

<!-- sdn-diagram:id=validation_utils_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=validation_utils_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

validation_utils_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=validation_utils_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 5 | 5 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Validation Utilities Specification

This specification covers basic validation utility functions for common data validation tasks: 1. Number range validation (positive, negative, in-range) 2. String validation (not empty) 3. Type-specific validation helpers 4. Common validation patterns

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #VALIDATION-001 to #VALIDATION-010 |
| Category | Tooling \| Data Validation |
| Difficulty | 1/5 |
| Status | Complete |
| Source | `test/01_unit/app/tooling/validation_utils_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

This specification covers basic validation utility functions for common data validation tasks:
1. Number range validation (positive, negative, in-range)
2. String validation (not empty)
3. Type-specific validation helpers
4. Common validation patterns

## Key Concepts

| Concept | Description |
|---------|-------------|
| Positive | Value strictly greater than 0 |
| Negative | Value strictly less than 0 |
| Non-negative | Value greater than or equal to 0 |
| In Range | Value between min and max (inclusive) |
| Not Empty | String has non-zero length |

## Behavior

- Positive check: x > 0
- Negative check: x < 0
- Non-negative check: x >= 0
- Range check: x >= min AND x <= max (inclusive bounds)
- Empty check: length() > 0 for strings

## Scenarios

### Validation Utilities

### Number Validation

#### is_positive works

1. expect is positive
2. expect not is positive
3. expect not is positive


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect is_positive(5)
expect not is_positive(0)
expect not is_positive(-5)
```

</details>

#### is_negative works

1. expect is negative
2. expect not is negative
3. expect not is negative


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect is_negative(-5)
expect not is_negative(0)
expect not is_negative(5)
```

</details>

#### is_non_negative works

1. expect is non negative
2. expect is non negative
3. expect not is non negative


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect is_non_negative(0)
expect is_non_negative(5)
expect not is_non_negative(-5)
```

</details>

#### is_in_range works

1. expect is in range
2. expect not is in range
3. expect not is in range


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect is_in_range(x=5, min_val=0, max_val=10)
expect not is_in_range(x=-1, min_val=0, max_val=10)
expect not is_in_range(x=11, min_val=0, max_val=10)
```

</details>

### String Validation

#### is_not_empty works

1. expect is not empty
2. expect not is not empty


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect is_not_empty("hello")
expect not is_not_empty("")
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 5 |
| Active scenarios | 5 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
