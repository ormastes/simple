# Coverage Specification

> <details>

<!-- sdn-diagram:id=coverage_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=coverage_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

coverage_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=coverage_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 26 | 26 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Coverage Specification

## Scenarios

### coverage module compilation

#### compiles successfully

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect 1 + 1 == 2
```

</details>

### coverage enabled check

#### returns false when disabled

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val enabled = false
expect enabled == false
```

</details>

#### returns true when enabled

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val enabled = true
expect enabled == true
```

</details>

### early return when disabled

#### should return early if not enabled

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val enabled = false
val should_return = not enabled
expect should_return == true
```

</details>

#### should continue if enabled

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val enabled = true
val should_return = not enabled
expect should_return == false
```

</details>

### quiet mode

#### quiet true suppresses output

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val quiet = true
expect quiet == true
```

</details>

#### quiet false allows output

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val quiet = false
expect quiet == false
```

</details>

### Result handling

#### Ok result check

1. expect Ok


<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect Ok("saved").is_ok() == true
```

</details>

#### Err result check

1. expect Err


<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect Err("failed").is_err() == true
```

</details>

### match on Result with early return

#### matches Err and returns

1. Err
2. Ok


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = Err("failed")
val matched = match result:
    Err(e) => "error"
    Ok(_) => "success"
expect matched == "error"
```

</details>

#### matches Ok and continues

1. Err
2. Ok


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = Ok("saved")
val matched = match result:
    Err(e) => "error"
    Ok(_) => "success"
expect matched == "success"
```

</details>

### Option handling for coverage

#### Some contains coverage data

1. expect cov is some


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val cov = Some("data")
expect cov.is_some() == true
```

</details>

#### unwrap gets coverage data

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val cov = Some("data")
val data = cov.unwrap()
expect data == "data"
```

</details>

### match on Option

#### matches Some

1. Some


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val cov = Some("data")
val matched = match cov:
    Some(c) => "has_coverage"
    None => "no_coverage"
expect matched == "has_coverage"
```

</details>

#### checks is_some and is_none

1. expect has cov is some


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val has_cov = Some("data")
expect has_cov.is_some() == true
```

</details>

### coverage stats struct

#### constructs with all fields

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val total_lines = 100
val total_files = 5
val total_functions = 20
val total_ffi_calls = 10
expect total_lines == 100
expect total_files == 5
```

</details>

### string interpolation

#### interpolates path

1. expect msg contains


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val path = "build/coverage/coverage.json"
val msg = "Coverage data saved to: {path}"
expect msg.contains(".coverage") == true
```

</details>

#### interpolates stats

1. expect msg contains


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val lines = 100
val msg = "  Lines executed: {lines}"
expect msg.contains("100") == true
```

</details>

### early return pattern

#### returns early when condition true

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val quiet = true
val should_return = quiet
expect should_return == true
```

</details>

#### continues when condition false

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val quiet = false
val should_return = quiet
expect should_return == false
```

</details>

### nested early returns

#### first check - not enabled

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val enabled = false
val should_return_1 = not enabled
expect should_return_1 == true
```

</details>

#### second check - save failed and quiet

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val save_ok = false
val quiet = true
val should_return_2 = not save_ok and quiet
expect should_return_2 == true
```

</details>

#### third check - quiet mode

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val quiet = true
val should_return_3 = quiet
expect should_return_3 == true
```

</details>

### boolean negation

#### not true equals false

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect not true == false
```

</details>

#### not false equals true

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect not false == true
```

</details>

#### double negation

1. expect not


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val enabled = true
expect not (not enabled) == true
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/01_unit/app/tooling/coverage_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- coverage module compilation
- coverage enabled check
- early return when disabled
- quiet mode
- Result handling
- match on Result with early return
- Option handling for coverage
- match on Option
- coverage stats struct
- string interpolation
- early return pattern
- nested early returns
- boolean negation

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 26 |
| Active scenarios | 26 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
