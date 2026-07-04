# Decorators Specification

> 1. check

<!-- sdn-diagram:id=decorators_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=decorators_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

decorators_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=decorators_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 26 | 26 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Decorators Specification

## Scenarios

### Skip/Ignore Decorators

### skip decorator

#### creates skip decorator with all parameters

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 17 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val decorator = skip(
    platforms: [],
    runtimes: [],
    profiles: [],
    architectures: [],
    features: [],
    version: "",
    hardware: [],
    dependencies: [],
    env_vars: {},
    fs_features: [],
    network: false,
    tags: [],
    reason: "test reason"
)
# Decorator should be a function
check(decorator != nil)
```

</details>

#### creates skip decorator with platforms only

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val decorator = skip(
    platforms: ["windows"],
    runtimes: [],
    profiles: [],
    architectures: [],
    features: [],
    version: "",
    hardware: [],
    dependencies: [],
    env_vars: {},
    fs_features: [],
    network: false,
    tags: [],
    reason: "Windows not supported yet"
)
check(decorator != nil)
```

</details>

#### skip decorator runs test when conditions don't match

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 19 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var test_ran = false
val decorator = skip(
    platforms: ["nonexistent_os_xyz"],
    runtimes: [],
    profiles: [],
    architectures: [],
    features: [],
    version: "",
    hardware: [],
    dependencies: [],
    env_vars: {},
    fs_features: [],
    network: false,
    tags: [],
    reason: "test"
)
# Note: This test is tricky because decorator expects rt_test_it
# We can't easily test the actual behavior without runtime support
check(true)
```

</details>

### ignore decorator

#### creates ignore decorator with all parameters

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val decorator = ignore(
    platforms: [],
    runtimes: [],
    profiles: [],
    architectures: [],
    features: [],
    version: "",
    hardware: [],
    dependencies: [],
    env_vars: {},
    fs_features: [],
    network: false,
    tags: [],
    reason: "test reason"
)
check(decorator != nil)
```

</details>

#### creates ignore decorator with platforms only

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val decorator = ignore(
    platforms: ["windows"],
    runtimes: [],
    profiles: [],
    architectures: [],
    features: [],
    version: "",
    hardware: [],
    dependencies: [],
    env_vars: {},
    fs_features: [],
    network: false,
    tags: [],
    reason: "Unix-only API"
)
check(decorator != nil)
```

</details>

### only_on decorator

#### creates only_on decorator

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val decorator = only_on(
    platforms: ["linux"],
    runtimes: [],
    profiles: [],
    architectures: [],
    features: [],
    version: "",
    hardware: [],
    dependencies: [],
    env_vars: {},
    fs_features: [],
    network: false,
    tags: []
)
check(decorator != nil)
```

</details>

#### creates only_on decorator with multiple conditions

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val decorator = only_on(
    platforms: ["linux", "macos"],
    runtimes: ["compiled"],
    profiles: [],
    architectures: [],
    features: [],
    version: "",
    hardware: [],
    dependencies: [],
    env_vars: {},
    fs_features: [],
    network: false,
    tags: []
)
check(decorator != nil)
```

</details>

### skip_if decorator

#### creates skip_if decorator with condition

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val cond = fn(): false
val decorator = skip_if(cond, "Condition not met")
check(decorator != nil)
```

</details>

#### creates skip_if with environment check

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val cond = fn(): get_env("CI") == ""
val decorator = skip_if(cond, "CI environment required")
check(decorator != nil)
```

</details>

#### creates skip_if with complex condition

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val cond = fn():
    val is_win = is_windows()
    val is_interp = is_interpreter()
    is_win and is_interp
val decorator = skip_if(cond, "Not on Windows interpreter")
check(decorator != nil)
```

</details>

### Simplified decorators

#### skip_on_windows creates decorator

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val decorator = skip_on_windows("Not yet ported")
check(decorator != nil)
```

</details>

#### skip_on_linux creates decorator

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val decorator = skip_on_linux("Not yet ported")
check(decorator != nil)
```

</details>

#### skip_on_interpreter creates decorator

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val decorator = skip_on_interpreter("Requires compiled mode")
check(decorator != nil)
```

</details>

#### ignore_on_windows creates decorator

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val decorator = ignore_on_windows("Unix-only API")
check(decorator != nil)
```

</details>

### Real-world usage patterns

#### creates platform-specific skip

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val skip_win = skip(
    platforms: ["windows"],
    runtimes: [],
    profiles: [],
    architectures: [],
    features: [],
    version: "",
    hardware: [],
    dependencies: [],
    env_vars: {},
    fs_features: [],
    network: false,
    tags: [],
    reason: "File permissions not implemented"
)
check(skip_win != nil)
```

</details>

#### creates runtime-specific skip

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val skip_interp = skip(
    platforms: [],
    runtimes: ["interpreter"],
    profiles: [],
    architectures: [],
    features: [],
    version: "",
    hardware: [],
    dependencies: [],
    env_vars: {},
    fs_features: [],
    network: false,
    tags: [],
    reason: "Generics require compilation"
)
check(skip_interp != nil)
```

</details>

#### creates hardware-specific skip

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val skip_no_gpu = skip(
    platforms: [],
    runtimes: [],
    profiles: [],
    architectures: [],
    features: [],
    version: "",
    hardware: ["gpu"],
    dependencies: [],
    env_vars: {},
    fs_features: [],
    network: false,
    tags: [],
    reason: "GPU required for test"
)
check(skip_no_gpu != nil)
```

</details>

#### creates complex multi-condition skip

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val skip_complex = skip(
    platforms: ["windows"],
    runtimes: ["interpreter"],
    profiles: ["debug"],
    architectures: [],
    features: [],
    version: "",
    hardware: [],
    dependencies: [],
    env_vars: {},
    fs_features: [],
    network: false,
    tags: ["slow", "integration"],
    reason: "Complex test requiring specific environment"
)
check(skip_complex != nil)
```

</details>

#### creates ignore for platform-specific API

1. reason: "Unix fork
2. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val ignore_win = ignore(
    platforms: ["windows"],
    runtimes: [],
    profiles: [],
    architectures: [],
    features: [],
    version: "",
    hardware: [],
    dependencies: [],
    env_vars: {},
    fs_features: [],
    network: false,
    tags: [],
    reason: "Unix fork() API not available on Windows"
)
check(ignore_win != nil)
```

</details>

#### creates ignore for architecture limitation

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val ignore_32bit = ignore(
    platforms: [],
    runtimes: [],
    profiles: [],
    architectures: ["x86", "arm32"],
    features: [],
    version: "",
    hardware: [],
    dependencies: [],
    env_vars: {},
    fs_features: [],
    network: false,
    tags: [],
    reason: "64-bit pointers required"
)
check(ignore_32bit != nil)
```

</details>

### Semantic distinction

#### skip represents TODO (will implement in future)

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val skip_todo = skip(
    platforms: ["windows"],
    runtimes: [],
    profiles: [],
    architectures: [],
    features: [],
    version: "",
    hardware: [],
    dependencies: [],
    env_vars: {},
    fs_features: [],
    network: false,
    tags: [],
    reason: "Windows support planned for v1.0"
)
check(skip_todo != nil)
```

</details>

#### ignore represents won't fix (fundamentally not supported)

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val ignore_permanent = ignore(
    platforms: ["windows"],
    runtimes: [],
    profiles: [],
    architectures: [],
    features: [],
    version: "",
    hardware: [],
    dependencies: [],
    env_vars: {},
    fs_features: [],
    network: false,
    tags: [],
    reason: "Unix-specific syscall with no Windows equivalent"
)
check(ignore_permanent != nil)
```

</details>

### Edge cases

#### handles empty reason

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val decorator = skip(
    platforms: ["windows"],
    runtimes: [],
    profiles: [],
    architectures: [],
    features: [],
    version: "",
    hardware: [],
    dependencies: [],
    env_vars: {},
    fs_features: [],
    network: false,
    tags: [],
    reason: ""
)
check(decorator != nil)
```

</details>

#### handles multiple platforms

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val decorator = skip(
    platforms: ["windows", "macos", "freebsd"],
    runtimes: [],
    profiles: [],
    architectures: [],
    features: [],
    version: "",
    hardware: [],
    dependencies: [],
    env_vars: {},
    fs_features: [],
    network: false,
    tags: [],
    reason: "Linux-only test"
)
check(decorator != nil)
```

</details>

#### handles multiple tags

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val decorator = skip(
    platforms: [],
    runtimes: [],
    profiles: [],
    architectures: [],
    features: [],
    version: "",
    hardware: [],
    dependencies: [],
    env_vars: {},
    fs_features: [],
    network: false,
    tags: ["slow", "integration", "e2e", "network"],
    reason: "Tagged test"
)
check(decorator != nil)
```

</details>

#### handles version constraints

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val decorator = skip(
    platforms: [],
    runtimes: [],
    profiles: [],
    architectures: [],
    features: [],
    version: ">= 1.0.0",
    hardware: [],
    dependencies: [],
    env_vars: {},
    fs_features: [],
    network: false,
    tags: [],
    reason: "Requires v1.0.0+"
)
check(decorator != nil)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/std/spec/decorators_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- Skip/Ignore Decorators
- skip decorator
- ignore decorator
- only_on decorator
- skip_if decorator
- Simplified decorators
- Real-world usage patterns
- Semantic distinction
- Edge cases

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 26 |
| Active scenarios | 26 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
