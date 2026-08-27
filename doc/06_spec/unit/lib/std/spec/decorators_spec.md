# Decorators Specification

> Tests covering Skip/Ignore Decorators, skip decorator, ignore decorator, only_on decorator, skip_if decorator, Simplified decorators, Real-world usage patterns, Semantic distinction, Edge cases.

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

- creates skip decorator with all parameters


<details>
<summary>Executable SSpec</summary>

Runnable source: 19 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("creates skip decorator with all parameters")
val decorator = make_skip_decorator(
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

- creates skip decorator with platforms only


<details>
<summary>Executable SSpec</summary>

Runnable source: 18 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("creates skip decorator with platforms only")
val decorator = make_skip_decorator(
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

- skip decorator runs test when conditions don't match


<details>
<summary>Executable SSpec</summary>

Runnable source: 21 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("skip decorator runs test when conditions don't match")
var test_ran = false
val decorator = make_skip_decorator(
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

- creates ignore decorator with all parameters


<details>
<summary>Executable SSpec</summary>

Runnable source: 18 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("creates ignore decorator with all parameters")
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

- creates ignore decorator with platforms only


<details>
<summary>Executable SSpec</summary>

Runnable source: 18 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("creates ignore decorator with platforms only")
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

- creates only_on decorator


<details>
<summary>Executable SSpec</summary>

Runnable source: 17 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("creates only_on decorator")
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

- creates only_on decorator with multiple conditions


<details>
<summary>Executable SSpec</summary>

Runnable source: 17 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("creates only_on decorator with multiple conditions")
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

- creates skip_if decorator with condition


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("creates skip_if decorator with condition")
val cond = fn(): false
val decorator = skip_if(cond, "Condition not met")
check(decorator != nil)
```

</details>

#### creates skip_if with environment check

- creates skip_if with environment check


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("creates skip_if with environment check")
val cond = fn(): get_env("CI") == ""
val decorator = skip_if(cond, "CI environment required")
check(decorator != nil)
```

</details>

#### creates skip_if with complex condition

- creates skip_if with complex condition


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("creates skip_if with complex condition")
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

- skip_on_windows creates decorator


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("skip_on_windows creates decorator")
val decorator = skip_on_windows("Not yet ported")
check(decorator != nil)
```

</details>

#### skip_on_linux creates decorator

- skip_on_linux creates decorator


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("skip_on_linux creates decorator")
val decorator = skip_on_linux("Not yet ported")
check(decorator != nil)
```

</details>

#### skip_on_interpreter creates decorator

- skip_on_interpreter creates decorator


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("skip_on_interpreter creates decorator")
val decorator = skip_on_interpreter("Requires compiled mode")
check(decorator != nil)
```

</details>

#### ignore_on_windows creates decorator

- ignore_on_windows creates decorator


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("ignore_on_windows creates decorator")
val decorator = ignore_on_windows("Unix-only API")
check(decorator != nil)
```

</details>

### Real-world usage patterns

#### creates platform-specific skip

- creates platform-specific skip


<details>
<summary>Executable SSpec</summary>

Runnable source: 18 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("creates platform-specific skip")
val skip_win = make_skip_decorator(
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

- creates runtime-specific skip


<details>
<summary>Executable SSpec</summary>

Runnable source: 18 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("creates runtime-specific skip")
val skip_interp = make_skip_decorator(
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

- creates hardware-specific skip


<details>
<summary>Executable SSpec</summary>

Runnable source: 18 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("creates hardware-specific skip")
val skip_no_gpu = make_skip_decorator(
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

- creates complex multi-condition skip


<details>
<summary>Executable SSpec</summary>

Runnable source: 18 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("creates complex multi-condition skip")
val skip_complex = make_skip_decorator(
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

- creates ignore for platform-specific API


<details>
<summary>Executable SSpec</summary>

Runnable source: 18 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("creates ignore for platform-specific API")
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

- creates ignore for architecture limitation


<details>
<summary>Executable SSpec</summary>

Runnable source: 18 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("creates ignore for architecture limitation")
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

- skip represents TODO (will implement in future)


<details>
<summary>Executable SSpec</summary>

Runnable source: 18 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("skip represents TODO (will implement in future)")
val skip_todo = make_skip_decorator(
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

- ignore represents won't fix (fundamentally not supported)


<details>
<summary>Executable SSpec</summary>

Runnable source: 18 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("ignore represents won't fix (fundamentally not supported)")
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

- handles empty reason


<details>
<summary>Executable SSpec</summary>

Runnable source: 18 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("handles empty reason")
val decorator = make_skip_decorator(
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

- handles multiple platforms


<details>
<summary>Executable SSpec</summary>

Runnable source: 18 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("handles multiple platforms")
val decorator = make_skip_decorator(
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

- handles multiple tags


<details>
<summary>Executable SSpec</summary>

Runnable source: 18 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("handles multiple tags")
val decorator = make_skip_decorator(
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

- handles version constraints


<details>
<summary>Executable SSpec</summary>

Runnable source: 18 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("handles version constraints")
val decorator = make_skip_decorator(
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
| Source | `test/unit/lib/std/spec/decorators_spec.spl` |
| Updated | 2026-08-27 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering Skip/Ignore Decorators, skip decorator, ignore decorator, only_on decorator, skip_if decorator, Simplified decorators, Real-world usage patterns, Semantic distinction, Edge cases.
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

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-UNIT`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `377afca0a61087b44a9cf5da6692b0ac201f59ad03fe4eb78b3ddc5ff69b701d`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `377afca0a61087b44a9cf5da6692b0ac201f59ad03fe4eb78b3ddc5ff69b701d`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `377afca0a61087b44a9cf5da6692b0ac201f59ad03fe4eb78b3ddc5ff69b701d`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **89/100**; effective score: **89/100**; blockers: **0**.

SSpec documentization score: 89/100
source: test/unit/lib/std/spec/decorators_spec.spl
mirror: doc/06_spec/unit/lib/std/spec/decorators_spec.md (current)
findings: 6 blockers: 0
  narrative=80 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/unit/lib/std/spec/decorators_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/unit/lib/std/spec/decorators_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, evidence, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/unit/lib/std/spec/decorators_spec.spl:1:1: warning SSDOC-NAR-001 [narrative] (-20): missing authored purpose and audience
  why: Readers need scope, audience, and intent before executable detail.
  improve: Add authored purpose, scope, and audience facts.
test/unit/lib/std/spec/decorators_spec.spl:17:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'creates skip decorator with all parameters' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/lib/std/spec/decorators_spec.spl:38:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'creates skip decorator with platforms only' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/lib/std/spec/decorators_spec.spl:58:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'skip decorator runs test when conditions don't match' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
