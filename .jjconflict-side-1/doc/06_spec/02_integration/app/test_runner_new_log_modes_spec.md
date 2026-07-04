# Test Runner New Log Modes Specification

> <details>

<!-- sdn-diagram:id=test_runner_new_log_modes_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=test_runner_new_log_modes_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

test_runner_new_log_modes_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=test_runner_new_log_modes_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 7 | 7 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Test Runner New Log Modes Specification

## Scenarios

### test runner new log mode CLI options

#### shows shared log options in help

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val (out, err, code) = _run_test_runner_new(["--help"])
expect(code).to_equal(0)
expect(out).to_contain("Simple Test Runner")
expect(out).to_contain("--log-mode")
expect(out).to_contain("--progress")
```

</details>

#### supports json default planning output

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val (out, err, code) = _run_test_runner_new(["--log-mode=json"])
expect(code).to_equal(0)
expect(out).to_contain("\"command\":\"test-runner-new\"")
expect(out).to_contain("\"status\":\"planned\"")
expect(out).to_contain("\"target\":\"test\"")
```

</details>

#### supports json target and mode planning

<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val (out, err, code) = _run_test_runner_new([
    "--log-mode=json",
    "test/unit",
    "--mode",
    "native",
    "--list",
    "--coverage"
])
expect(code).to_equal(0)
expect(out).to_contain("\"target\":\"test/unit\"")
expect(out).to_contain("\"mode\":\"native\"")
expect(out).to_contain("\"listOnly\":true")
expect(out).to_contain("\"coverage\":true")
```

</details>

#### supports compile shorthand mode planning

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val (out, err, code) = _run_test_runner_new(["--log-mode=json", "--compile"])
expect(code).to_equal(0)
expect(out).to_contain("\"mode\":\"native\"")
```

</details>

#### supports dot progress for help output

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val (out, err, code) = _run_test_runner_new(["--progress=dot", "--help"])
expect(code).to_equal(0)
expect(out).to_contain(".\nSimple Test Runner")
```

</details>

#### rejects invalid log mode

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val (out, err, code) = _run_test_runner_new(["--log-mode=noisy"])
expect(code).to_equal(1)
```

</details>

#### renders json unknown option output

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val (out, err, code) = _run_test_runner_new(["--log-mode=json", "--surprise"])
expect(code).to_equal(1)
expect(out).to_contain("\"status\":\"error\"")
expect(out).to_contain("Unknown test runner option: --surprise")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/02_integration/app/test_runner_new_log_modes_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- test runner new log mode CLI options

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 7 |
| Active scenarios | 7 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
