# Multi Mode Test Runner Specification

> <details>

<!-- sdn-diagram:id=multi_mode_test_runner_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=multi_mode_test_runner_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

multi_mode_test_runner_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=multi_mode_test_runner_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 34 | 34 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Multi Mode Test Runner Specification

## Scenarios

### Multi-Mode Test Runner Unit Tests

### TestExecutionMode

#### has Interpreter variant

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val mode = TestExecutionMode.Interpreter
val name = execution_mode_to_string(mode)
expect(name).to_equal("interpreter")
```

</details>

#### has Smf variant

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val mode = TestExecutionMode.Smf
val name = execution_mode_to_string(mode)
expect(name).to_equal("smf")
```

</details>

#### has Native variant

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val mode = TestExecutionMode.Native
val name = execution_mode_to_string(mode)
expect(name).to_equal("native")
```

</details>

#### has AllModes variant

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val mode = TestExecutionMode.AllModes
val name = execution_mode_to_string(mode)
expect(name).to_equal("all-modes")
```

</details>

#### composite is detected correctly

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val mode = TestExecutionMode.Composite("baremetal(riscv32)")
expect(execution_mode_is_composite(mode)).to_equal(true)
```

</details>

#### non-composite is detected correctly

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val mode = TestExecutionMode.Interpreter
expect(execution_mode_is_composite(mode)).to_equal(false)
```

</details>

### execution_mode_from_string

#### parses interpreter

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val mode = execution_mode_from_string("interpreter")
expect(execution_mode_to_string(mode)).to_equal("interpreter")
```

</details>

#### parses native

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val mode = execution_mode_from_string("native")
expect(execution_mode_to_string(mode)).to_equal("native")
```

</details>

#### parses smf

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val mode = execution_mode_from_string("smf")
expect(execution_mode_to_string(mode)).to_equal("smf")
```

</details>

#### parses all

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val mode = execution_mode_from_string("all")
expect(execution_mode_to_string(mode)).to_equal("all-modes")
```

</details>

#### parses all-modes

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val mode = execution_mode_from_string("all-modes")
expect(execution_mode_to_string(mode)).to_equal("all-modes")
```

</details>

### parse_mode_str

#### parses native string

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val mode = parse_mode_str("native")
expect(execution_mode_to_string(mode)).to_equal("native")
```

</details>

#### parses binary as native

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val mode = parse_mode_str("binary")
expect(execution_mode_to_string(mode)).to_equal("native")
```

</details>

#### parses loader as smf

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val mode = parse_mode_str("loader")
expect(execution_mode_to_string(mode)).to_equal("smf")
```

</details>

#### parses smf

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val mode = parse_mode_str("smf")
expect(execution_mode_to_string(mode)).to_equal("smf")
```

</details>

#### parses all as all-modes

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val mode = parse_mode_str("all")
expect(execution_mode_to_string(mode)).to_equal("all-modes")
```

</details>

#### parses all-modes

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val mode = parse_mode_str("all-modes")
expect(execution_mode_to_string(mode)).to_equal("all-modes")
```

</details>

#### defaults to interpreter

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val mode = parse_mode_str("unknown")
expect(execution_mode_to_string(mode)).to_equal("interpreter")
```

</details>

### TestInitConfig

#### default has nil init_fn

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val config = test_init_config_default()
expect(config.init_fn.?).to_equal(false)
```

</details>

#### default has nil init_module

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val config = test_init_config_default()
expect(config.init_module.?).to_equal(false)
```

</details>

#### default timeout is 30000

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val config = test_init_config_default()
expect(config.timeout_ms).to_equal(30000)
```

</details>

#### with_module sets module path

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val config = test_init_config_with_module("test/init.spl")
expect(config.init_module.?).to_equal(true)
expect(config.init_module.unwrap()).to_equal("test/init.spl")
```

</details>

### TestFileResult

#### is_ok when no failures

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val r = make_passing_result("test.spl")
expect(r.is_ok()).to_equal(true)
```

</details>

#### is not ok when failures exist

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val r = make_failing_result("test.spl")
expect(r.is_ok()).to_equal(false)
```

</details>

### TestRunResult

#### is_ok when total_failed is zero

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val r = make_passing_run_result()
expect(r.is_ok()).to_equal(true)
```

</details>

#### is not ok when total_failed > 0

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val r = make_failing_run_result()
expect(r.is_ok()).to_equal(false)
```

</details>

### TestModeResult

#### is_ok delegates to inner result

1. result: make passing run result
   - Expected: mr.is_ok() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val mr = TestModeResult(
    mode: TestExecutionMode.Interpreter,
    result: make_passing_run_result(),
    duration_ms: 100
)
expect(mr.is_ok()).to_equal(true)
```

</details>

#### is not ok when inner result has failures

1. result: make failing run result
   - Expected: mr.is_ok() is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val mr = TestModeResult(
    mode: TestExecutionMode.Native,
    result: make_failing_run_result(),
    duration_ms: 200
)
expect(mr.is_ok()).to_equal(false)
```

</details>

### TestAllModesResult

#### summary contains mode names

1. result: make passing run result


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val mr1 = TestModeResult(
    mode: TestExecutionMode.Interpreter,
    result: make_passing_run_result(),
    duration_ms: 100
)
val all = TestAllModesResult(mode_results: [mr1], all_passed: true)
val s = all.summary()
expect(s).to_contain("interpreter")
```

</details>

#### summary contains pass/fail counts

1. result: make passing run result


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val mr1 = TestModeResult(
    mode: TestExecutionMode.Interpreter,
    result: make_passing_run_result(),
    duration_ms: 100
)
val all = TestAllModesResult(mode_results: [mr1], all_passed: true)
val s = all.summary()
expect(s).to_contain("5 passed")
expect(s).to_contain("0 failed")
```

</details>

### parse_test_args

#### parses --mode=native

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val opts = parse_test_args(["--mode=native", "test/"])
expect(execution_mode_to_string(opts.mode)).to_equal("native")
```

</details>

#### parses --mode=loader

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val opts = parse_test_args(["--mode=loader", "test/"])
expect(execution_mode_to_string(opts.mode)).to_equal("smf")
```

</details>

#### parses --all-modes

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val opts = parse_test_args(["--all-modes", "test/"])
expect(execution_mode_to_string(opts.mode)).to_equal("all-modes")
```

</details>

#### defaults to interpreter mode

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val opts = parse_test_args(["test/"])
expect(execution_mode_to_string(opts.mode)).to_equal("interpreter")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/01_unit/multi_mode_test_runner_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- Multi-Mode Test Runner Unit Tests
- TestExecutionMode
- execution_mode_from_string
- parse_mode_str
- TestInitConfig
- TestFileResult
- TestRunResult
- TestModeResult
- TestAllModesResult
- parse_test_args

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 34 |
| Active scenarios | 34 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
