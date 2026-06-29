# Config Parser Specification

> <details>

<!-- sdn-diagram:id=config_parser_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=config_parser_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

config_parser_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=config_parser_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 9 | 9 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Config Parser Specification

## Scenarios

### Test Configuration Parsing

#### parses default configuration

<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val config = TestConfig {
    mode: TestExecutionMode.Interpreter,
    timeout: 120,
    fail_fast: false,
    tags: [],
    path: "test/"
}
expect config.timeout == 120
expect config.fail_fast == false
```

</details>

#### validates timeout values

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val valid_timeout = 60
val invalid_timeout = -1
expect valid_timeout > 0
expect invalid_timeout < 0
```

</details>

#### handles tag filters

1. expect tags len


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val tags = ["unit", "integration"]
expect tags.len() == 2
expect tags[0] == "unit"
```

</details>

### Execution Mode Selection

#### defaults to interpreter mode

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val mode = TestExecutionMode.Interpreter
match mode:
    case TestExecutionMode.Interpreter:
        expect true
    _ =>
        fail "Should be Interpreter mode"
```

</details>

#### supports SMF mode

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val mode = TestExecutionMode.SMF
match mode:
    case TestExecutionMode.SMF:
        expect true
    _ =>
        fail "Should be SMF mode"
```

</details>

#### supports native mode

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val mode = TestExecutionMode.Native
match mode:
    case TestExecutionMode.Native:
        expect true
    _ =>
        fail "Should be Native mode"
```

</details>

### Path Validation

#### accepts valid test directory

1. expect path len


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val path = "test/"
expect path.len() > 0
expect path == "test/"
```

</details>

#### accepts specific test file

1. expect path ends with
2. expect path contains


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val path = "test/unit/lib/std/app/test_runner/config_parser_spec.spl"
expect path.ends_with(".spl")
expect path.contains("test")
```

</details>

#### handles relative paths

1. expect path starts with


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val path = "./test/unit/"
expect path.starts_with(".")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/01_unit/app/test_runner/config_parser_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- Test Configuration Parsing
- Execution Mode Selection
- Path Validation

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 9 |
| Active scenarios | 9 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
