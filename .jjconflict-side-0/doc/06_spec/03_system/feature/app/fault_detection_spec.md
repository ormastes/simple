# Fault Detection

> Tests the runtime fault detection system including null pointer checks, out-of-bounds access, division by zero, and stack overflow detection. Verifies that faults are caught gracefully with descriptive error messages and proper stack traces.

<!-- sdn-diagram:id=fault_detection_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=fault_detection_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

fault_detection_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=fault_detection_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 36 | 36 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Fault Detection

Tests the runtime fault detection system including null pointer checks, out-of-bounds access, division by zero, and stack overflow detection. Verifies that faults are caught gracefully with descriptive error messages and proper stack traces.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | In Progress |
| Source | `test/03_system/feature/app/fault_detection_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests the runtime fault detection system including null pointer checks, out-of-bounds
access, division by zero, and stack overflow detection. Verifies that faults are
caught gracefully with descriptive error messages and proper stack traces.

## Scenarios

### Fault Detection - FFI API

#### stack overflow detection

#### enables detection and allows shallow recursion

1. rt fault set stack overflow detection
2. rt fault set max recursion depth
   - Expected: result equals `5`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
rt_fault_set_stack_overflow_detection(true)
rt_fault_set_max_recursion_depth(1000)
val result = shallow_recurse(5)
expect(result).to_equal(5)
```

</details>

#### allows zero-depth call

1. rt fault set stack overflow detection
   - Expected: result equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
rt_fault_set_stack_overflow_detection(true)
val result = shallow_recurse(0)
expect(result).to_equal(0)
```

</details>

#### allows single recursion step

1. rt fault set stack overflow detection
   - Expected: result equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
rt_fault_set_stack_overflow_detection(true)
val result = shallow_recurse(1)
expect(result).to_equal(1)
```

</details>

#### works when disabled

1. rt fault set stack overflow detection
   - Expected: result equals `5`
2. rt fault set stack overflow detection


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
rt_fault_set_stack_overflow_detection(false)
val result = shallow_recurse(5)
expect(result).to_equal(5)
rt_fault_set_stack_overflow_detection(true)
```

</details>

#### depth limit configuration

#### accepts small depth limit

1. rt fault set max recursion depth
   - Expected: result equals `3`
2. rt fault set max recursion depth


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
rt_fault_set_max_recursion_depth(100)
val result = shallow_recurse(3)
expect(result).to_equal(3)
rt_fault_set_max_recursion_depth(1000)
```

</details>

#### accepts large depth limit

1. rt fault set max recursion depth
   - Expected: result equals `10`
2. rt fault set max recursion depth


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
rt_fault_set_max_recursion_depth(50000)
val result = iterative_sum(10)
expect(result).to_equal(10)
rt_fault_set_max_recursion_depth(1000)
```

</details>

#### timeout configuration

#### disables timeout with zero

1. rt fault set timeout
   - Expected: result equals `10`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
rt_fault_set_timeout(0)
val result = iterative_sum(10)
expect(result).to_equal(10)
```

</details>

#### sets large timeout without affecting fast code

1. rt fault set timeout
   - Expected: result equals `10`
2. rt fault set timeout


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
rt_fault_set_timeout(60)
val result = iterative_sum(10)
expect(result).to_equal(10)
rt_fault_set_timeout(0)
```

</details>

#### execution limit configuration

#### sets execution limit

1. rt fault set execution limit
   - Expected: result equals `10`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
rt_fault_set_execution_limit(1000000)
val result = iterative_sum(10)
expect(result).to_equal(10)
```

</details>

#### disables execution limit with zero

1. rt fault set execution limit
   - Expected: result equals `10`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
rt_fault_set_execution_limit(0)
val result = iterative_sum(10)
expect(result).to_equal(10)
```

</details>

### Fault Detection - Simple API

#### enable/disable stack overflow

#### enables detection

1. enable stack overflow detection
   - Expected: result equals `3`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
enable_stack_overflow_detection()
val result = shallow_recurse(3)
expect(result).to_equal(3)
```

</details>

#### disables detection

1. disable stack overflow detection
   - Expected: result equals `3`
2. enable stack overflow detection


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
disable_stack_overflow_detection()
val result = shallow_recurse(3)
expect(result).to_equal(3)
enable_stack_overflow_detection()
```

</details>

#### set_recursion_limit

#### sets a custom limit

1. set recursion limit
   - Expected: result equals `3`
2. reset defaults


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
set_recursion_limit(200)
val result = shallow_recurse(3)
expect(result).to_equal(3)
reset_defaults()
```

</details>

#### set_timeout

#### sets and clears timeout

1. set timeout
   - Expected: result equals `5`
2. set timeout


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
set_timeout(60)
val result = iterative_sum(5)
expect(result).to_equal(5)
set_timeout(0)
```

</details>

#### set_execution_limit

#### sets a custom limit

1. set execution limit
   - Expected: result equals `5`
2. reset defaults


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
set_execution_limit(5000000)
val result = iterative_sum(5)
expect(result).to_equal(5)
reset_defaults()
```

</details>

#### reset_defaults

#### restores default configuration

1. set recursion limit
2. set timeout
3. set execution limit
4. reset defaults
   - Expected: result equals `3`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
set_recursion_limit(50)
set_timeout(10)
set_execution_limit(100)
reset_defaults()
# After reset, normal operations should work
val result = shallow_recurse(3)
expect(result).to_equal(3)
```

</details>

### Fault Detection - FaultConfig

#### preset configurations

#### creates default config

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val config = FaultConfig.defaults()
expect(config.stack_overflow_enabled).to_equal(true)
expect(config.max_recursion_depth).to_equal(1000)
expect(config.timeout_secs).to_equal(0)
expect(config.execution_limit).to_equal(10000000)
```

</details>

#### creates strict config

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val config = FaultConfig.strict()
expect(config.stack_overflow_enabled).to_equal(true)
expect(config.max_recursion_depth).to_equal(500)
expect(config.timeout_secs).to_equal(30)
expect(config.execution_limit).to_equal(5000000)
```

</details>

#### creates permissive config

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val config = FaultConfig.permissive()
expect(config.stack_overflow_enabled).to_equal(true)
expect(config.max_recursion_depth).to_equal(10000)
expect(config.timeout_secs).to_equal(0)
expect(config.execution_limit).to_equal(100000000)
```

</details>

#### creates disabled config

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val config = FaultConfig.disabled()
expect(config.stack_overflow_enabled).to_equal(false)
expect(config.max_recursion_depth).to_equal(0)
expect(config.timeout_secs).to_equal(0)
expect(config.execution_limit).to_equal(0)
```

</details>

#### config application

#### applies default config

1. config apply
   - Expected: result equals `3`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val config = FaultConfig.defaults()
config.apply()
val result = shallow_recurse(3)
expect(result).to_equal(3)
```

</details>

#### applies strict config

1. config apply
   - Expected: result equals `3`
2. set timeout
3. reset defaults


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val config = FaultConfig.strict()
config.apply()
val result = shallow_recurse(3)
expect(result).to_equal(3)
# Clean up timeout
set_timeout(0)
reset_defaults()
```

</details>

#### applies permissive config

1. config apply
   - Expected: result equals `5`
2. reset defaults


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val config = FaultConfig.permissive()
config.apply()
val result = shallow_recurse(5)
expect(result).to_equal(5)
reset_defaults()
```

</details>

#### applies disabled config and re-enables

1. config apply
   - Expected: result equals `3`
2. reset defaults


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val config = FaultConfig.disabled()
config.apply()
val result = shallow_recurse(3)
expect(result).to_equal(3)
reset_defaults()
```

</details>

#### config builders

#### creates config with custom timeout

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val config = FaultConfig.defaults().with_timeout(45)
expect(config.timeout_secs).to_equal(45)
expect(config.max_recursion_depth).to_equal(1000)
```

</details>

#### creates config with custom depth

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val config = FaultConfig.defaults().with_max_depth(2000)
expect(config.max_recursion_depth).to_equal(2000)
expect(config.timeout_secs).to_equal(0)
```

</details>

#### creates config with custom execution limit

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val config = FaultConfig.defaults().with_execution_limit(999)
expect(config.execution_limit).to_equal(999)
expect(config.max_recursion_depth).to_equal(1000)
```

</details>

#### chains multiple builders

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val config = FaultConfig.defaults().with_timeout(10).with_max_depth(200).with_execution_limit(500)
expect(config.timeout_secs).to_equal(10)
expect(config.max_recursion_depth).to_equal(200)
expect(config.execution_limit).to_equal(500)
```

</details>

### Fault Detection - Constants

#### has correct default max recursion depth

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(DEFAULT_MAX_RECURSION_DEPTH).to_equal(1000)
```

</details>

#### has correct default execution limit

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(DEFAULT_EXECUTION_LIMIT).to_equal(10000000)
```

</details>

#### has correct default timeout

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(DEFAULT_TIMEOUT).to_equal(0)
```

</details>

### Fault Detection - Functional

#### recursion with detection enabled

#### handles fibonacci computation

1. enable stack overflow detection
2. set recursion limit
   - Expected: result equals `21`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
enable_stack_overflow_detection()
set_recursion_limit(1000)
val result = fibonacci(8)
expect(result).to_equal(21)
```

</details>

#### handles multiple sequential recursive calls

1. enable stack overflow detection
   - Expected: r1 + r2 + r3 equals `10`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
enable_stack_overflow_detection()
val r1 = shallow_recurse(3)
val r2 = shallow_recurse(5)
val r3 = shallow_recurse(2)
expect(r1 + r2 + r3).to_equal(10)
```

</details>

#### iterative with detection enabled

<details>
<summary>Advanced: handles iterative loops</summary>

#### handles iterative loops

1. enable stack overflow detection
   - Expected: result equals `100`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
enable_stack_overflow_detection()
val result = iterative_sum(100)
expect(result).to_equal(100)
```

</details>


</details>

#### toggling detection during computation

#### toggle on-off-on preserves correctness

1. enable stack overflow detection
2. disable stack overflow detection
3. enable stack overflow detection
   - Expected: r1 equals `2`
   - Expected: r2 equals `2`
   - Expected: r3 equals `2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
enable_stack_overflow_detection()
val r1 = shallow_recurse(2)
disable_stack_overflow_detection()
val r2 = shallow_recurse(2)
enable_stack_overflow_detection()
val r3 = shallow_recurse(2)
expect(r1).to_equal(2)
expect(r2).to_equal(2)
expect(r3).to_equal(2)
```

</details>

#### combined features

#### all features active with fast code

1. config apply
   - Expected: result equals `21`
2. set timeout
3. reset defaults


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val config = FaultConfig(
    stack_overflow_enabled: true,
    max_recursion_depth: 500,
    timeout_secs: 60,
    execution_limit: 5000000)
config.apply()
val result = fibonacci(8)
expect(result).to_equal(21)
set_timeout(0)
reset_defaults()
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 36 |
| Active scenarios | 36 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
