# Process Limits Enforcement Specification

> <details>

<!-- sdn-diagram:id=process_limits_enforcement_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=process_limits_enforcement_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

process_limits_enforcement_spec -> app
process_limits_enforcement_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=process_limits_enforcement_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 14 | 14 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Process Limits Enforcement Specification

## Scenarios

### process_run_with_limits basic functionality

#### succeeds with simple command within limits

<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = process_run_with_limits(
    "echo",
    ["hello"],
    5000,
    100000000,
    5,
    100,
    10
)
expect(result.exit_code).to_equal(0)
expect(result.limit_exceeded).to_equal(false)
expect(result.limit_type).to_equal("")
expect(result.stdout).to_contain("hello")
```

</details>

#### returns ProcessResult with all fields

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = process_run_with_limits("pwd", [], 5000, 100000000, 5, 100, 10)
expect(result.stdout.len()).to_be_greater_than(0)
expect(result.exit_code).to_equal(0)
expect(result.limit_exceeded).to_equal(false)
```

</details>

### process_run_with_limits timeout enforcement

<details>
<summary>Advanced: detects timeout violation with sleep command</summary>

#### detects timeout violation with sleep command _(slow)_

<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = process_run_with_limits(
    "sleep",
    ["10"],
    1000,
    100000000,
    20,
    100,
    10
)
expect(result.limit_exceeded).to_equal(true)
expect(result.limit_type).to_equal("timeout")
```

</details>


</details>

<details>
<summary>Advanced: detects timeout with infinite loop</summary>

#### detects timeout with infinite loop _(slow)_

<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = process_run_with_limits(
    "bash",
    ["-c", "while true; do :; done"],
    2000,
    100000000,
    30,
    100,
    10
)
expect(result.limit_exceeded).to_equal(true)
expect(result.limit_type).to_equal("timeout")
```

</details>


</details>

### process_run_with_limits CPU limit enforcement

<details>
<summary>Advanced: detects CPU time limit violation</summary>

#### detects CPU time limit violation _(slow)_

<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
if is_windows():
    0
else:
    val result = process_run_with_limits(
        "bash",
        ["-c", "yes > /dev/null"],
        30000,
        100000000,
        2,
        100,
        10
    )
    expect(result.limit_exceeded).to_equal(true)
    val limit_ok = result.limit_type == "cpu" or result.limit_type == "timeout"
    expect(limit_ok).to_equal(true)
```

</details>


</details>

### process_run_with_limits memory limit enforcement

<details>
<summary>Advanced: detects memory limit violation with large allocation</summary>

#### detects memory limit violation with large allocation _(slow)_

<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
if is_windows():
    0
else:
    val result = process_run_with_limits(
        "python3",
        ["-c", "x = [0] * 100000000"],
        10000,
        10485760,
        10,
        100,
        10
    )
    val exceeded = result.limit_exceeded
    val is_mem_or_timeout = result.limit_type == "memory" or result.exit_code != 0
    expect(is_mem_or_timeout).to_equal(true)
```

</details>


</details>

### process_run_with_limits file descriptor enforcement

#### allows command within fd limits

<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
if is_windows():
    0
else:
    val result = process_run_with_limits(
        "bash",
        ["-c", "exec 3< /dev/null; exec 3>&-"],
        5000,
        100000000,
        5,
        100,
        10
    )
    expect(result.exit_code).to_equal(0)
```

</details>

### process_run_with_limits process count enforcement

#### allows command within process limits

<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
if is_windows():
    0
else:
    val result = process_run_with_limits(
        "bash",
        ["-c", "echo test"],
        5000,
        100000000,
        5,
        100,
        10
    )
    expect(result.exit_code).to_equal(0)
```

</details>

### process_run_with_limits edge cases

#### handles zero limits as unlimited

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = process_run_with_limits("echo", ["test"], 0, 0, 0, 0, 0)
expect(result.exit_code).to_equal(0)
expect(result.limit_exceeded).to_equal(false)
```

</details>

<details>
<summary>Advanced: does not inject a default wall timeout when timeout is disabled</summary>

#### does not inject a default wall timeout when timeout is disabled _(slow)_

<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = process_run_with_limits(
    "sleep",
    ["2"],
    0,
    0,
    0,
    0,
    0
)
expect(result.exit_code).to_equal(0)
expect(result.limit_exceeded).to_equal(false)
```

</details>


</details>

#### handles command with no arguments

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = process_run_with_limits("pwd", [], 5000, 100000000, 5, 100, 10)
expect(result.exit_code).to_equal(0)
```

</details>

#### handles command with multiple arguments

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = process_run_with_limits("ls", ["-la", "/tmp"], 5000, 100000000, 5, 100, 10)
expect(result.exit_code).to_equal(0)
```

</details>

#### detects failing command correctly

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = process_run_with_limits("ls", ["/nonexistent/path/12345"], 5000, 100000000, 5, 100, 10)
expect(result.exit_code).to_be_greater_than(0)
expect(result.limit_exceeded).to_equal(false)
```

</details>

### process_run_with_limits Windows fallback

#### uses timeout-only mode on Windows

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
if is_windows():
    val result = process_run_with_limits("cmd", ["/c", "echo test"], 5000, 100000000, 5, 100, 10)
    expect(result.exit_code).to_equal(0)
else:
    val dummy = 1
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/01_unit/app/io/process_limits_enforcement_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- process_run_with_limits basic functionality
- process_run_with_limits timeout enforcement
- process_run_with_limits CPU limit enforcement
- process_run_with_limits memory limit enforcement
- process_run_with_limits file descriptor enforcement
- process_run_with_limits process count enforcement
- process_run_with_limits edge cases
- process_run_with_limits Windows fallback

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 14 |
| Active scenarios | 14 |
| Slow scenarios | 5 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
