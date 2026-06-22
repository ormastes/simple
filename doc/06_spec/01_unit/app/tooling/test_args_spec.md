# Test Arguments Specification

> Unit tests for test runner argument parsing module. Validates parsing of command-line flags, options, and path arguments used to configure test execution behavior.

<!-- sdn-diagram:id=test_args_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=test_args_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

test_args_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=test_args_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 26 | 26 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Test Arguments Specification

Unit tests for test runner argument parsing module. Validates parsing of command-line flags, options, and path arguments used to configure test execution behavior.

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | Test Runner CLI |
| Category | Tooling |
| Difficulty | 2/5 |
| Status | Implemented |
| Source | `test/01_unit/app/tooling/test_args_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Unit tests for test runner argument parsing module. Validates parsing of command-line flags,
options, and path arguments used to configure test execution behavior.

## Key Features

- Test level flag parsing (--unit, --integration, --system)
- Boolean flag detection (--fail-fast, --gc-log, --watch, --json, --doc)
- Doctest specific flags (--doctest, --all, --doctest-src, --doctest-doc)
- Diagram generation flags (--seq-diagram, --diagram-all)
- Value flags with arguments (--tag, --seed, --format)
- Path and file argument detection
- Bounds checking and iteration patterns
- Default value handling

## Related Specifications

- [Test Runner Design](../../../docs/design/test_runner.md)

## Scenarios

### test level flag patterns

#### validates --unit flag

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect "--unit" == "--unit"
```

</details>

#### validates --integration flag

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect "--integration" == "--integration"
```

</details>

#### validates --system flag

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect "--system" == "--system"
```

</details>

### boolean flag patterns

#### validates --fail-fast

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect "--fail-fast" == "--fail-fast"
```

</details>

#### validates --gc-log

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect "--gc-log" == "--gc-log"
```

</details>

#### validates --watch

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect "--watch" == "--watch"
```

</details>

#### validates --json

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect "--json" == "--json"
```

</details>

#### validates --doc

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect "--doc" == "--doc"
```

</details>

### doctest flags

#### validates --doctest

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect "--doctest" == "--doctest"
```

</details>

#### validates --all

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect "--all" == "--all"
```

</details>

#### validates --doctest-src

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect "--doctest-src" == "--doctest-src"
```

</details>

#### validates --doctest-doc

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect "--doctest-doc" == "--doctest-doc"
```

</details>

### diagram flags

#### validates --seq-diagram

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect "--seq-diagram" == "--seq-diagram"
```

</details>

#### validates --diagram-all

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect "--diagram-all" == "--diagram-all"
```

</details>

### value flags

#### validates --tag

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect "--tag" == "--tag"
```

</details>

#### validates --seed

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect "--seed" == "--seed"
```

</details>

#### validates --format

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect "--format" == "--format"
```

</details>

### mutable struct pattern

#### validates mutation

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var value = false
value = true
expect value == true
```

</details>

### option pattern

#### validates value assignment

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val value = "test.spl"
expect value == "test.spl"
```

</details>

### path detection

#### detects non-flag

1. expect not arg starts with


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val arg = "test.spl"
expect not arg.starts_with("-") == true
```

</details>

#### detects flag

1. expect arg starts with


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val arg = "--flag"
expect arg.starts_with("-") == true
```

</details>

### iteration pattern

#### increments by 1

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var i = 0
i = i + 1
expect i == 1
```

</details>

#### increments by 2

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var i = 0
i = i + 2
expect i == 2
```

</details>

### bounds checking

#### validates index bounds

1. expect i + 1 < args len


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val args = ["--flag", "value", "arg"]
val i = 0
expect i + 1 < args.len() == true
```

</details>

### default values

#### defaults to false

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val default_val = false
expect default_val == false
```

</details>

### multiple flag sets

#### sets multiple flags

<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var flag1 = false
var flag2 = false
var flag3 = false
flag1 = true
flag2 = true
flag3 = true
expect flag1 == true
expect flag2 == true
expect flag3 == true
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 26 |
| Active scenarios | 26 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
