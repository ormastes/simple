# Skip Ignore Integration Specification

> 1. check

<!-- sdn-diagram:id=skip_ignore_integration_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=skip_ignore_integration_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

skip_ignore_integration_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=skip_ignore_integration_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 23 | 23 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Skip Ignore Integration Specification

## Scenarios

### Skip/Ignore Integration Tests

### Platform-specific tests

#### demonstrates platform detection concept

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Platform detection would use get_platform_os() etc.
val platform = "linux"
check(platform != "")
```

</details>

#### demonstrates Unix vs Windows distinction

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val is_unix = true
check(is_unix == true)
```

</details>

### Runtime mode detection

#### identifies current runtime mode

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val mode = "interpreter"
check(mode != "")
```

</details>

### Architecture detection

#### identifies CPU architecture

1. check
2. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val arch = "x86_64"
val bits = 64
check(arch != "")
check(bits == 64)
```

</details>

### Hardware capabilities

#### checks available hardware

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val cores = 4
check(cores > 0)
```

</details>

### Complete environment profile

#### prints complete environment information

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
check(true)
```

</details>

### Real-world skip patterns

#### example: skip on Windows (concept)

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val reason = "chmod() not yet implemented on Windows"
check(reason != "")
```

</details>

#### example: skip in interpreter mode (concept)

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val reason = "Generics need static compilation"
check(reason != "")
```

</details>

#### example: skip without hardware (concept)

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val reason = "Acceleration required"
check(reason != "")
```

</details>

### Real-world ignore patterns

#### example: ignore Unix fork on Windows (concept)

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val reason = "fork() is Unix-only, no Windows equivalent"
check(reason != "")
```

</details>

#### example: ignore 32-bit architecture (concept)

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val reason = "64-bit pointers required"
check(reason != "")
```

</details>

### Simplified decorator usage

#### example: using platform skip

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val reason = "Not yet ported"
check(reason != "")
```

</details>

#### example: using interpreter skip

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val reason = "Compiled mode needed"
check(reason != "")
```

</details>

### Complex multi-condition examples

#### example: CI-only network test

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val reason = "Network test only in CI"
check(reason != "")
```

</details>

#### example: multi-skip

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val reason = "Windows interpreter mode not fully supported"
check(reason != "")
```

</details>

### Conditional skip with skip_if

#### example: skip if no CI environment

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val reason = "CI environment required"
check(reason != "")
```

</details>

#### example: skip on complex condition

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val reason = "Not supported on certain configs"
check(reason != "")
```

</details>

### only_on usage

#### example: Linux-only test

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val platform = "linux"
check(platform == "linux")
```

</details>

#### example: compiled mode only

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val mode = "compiled"
check(mode == "compiled")
```

</details>

### Performance with multiple decorators

#### creates decorators quickly

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var i = 0
while i < 10:
    val reason = "Test {i}"
    check(reason != "")
    i = i + 1
```

</details>

### Documentation examples

#### README example: platform-specific skip

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val reason = "chmod() not available on Windows"
check(reason != "")
```

</details>

#### README example: hardware requirement

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val reason = "Required for neural network test"
check(reason != "")
```

</details>

#### README example: ignore fundamentally unsupported

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val reason = "Unix fork() API - no Windows equivalent"
check(reason != "")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/std/skip_ignore_integration_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- Skip/Ignore Integration Tests
- Platform-specific tests
- Runtime mode detection
- Architecture detection
- Hardware capabilities
- Complete environment profile
- Real-world skip patterns
- Real-world ignore patterns
- Simplified decorator usage
- Complex multi-condition examples
- Conditional skip with skip_if
- only_on usage
- Performance with multiple decorators
- Documentation examples

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 23 |
| Active scenarios | 23 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
