# Timeout Specification

> <details>

<!-- sdn-diagram:id=timeout_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=timeout_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

timeout_spec -> std
timeout_spec -> app
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=timeout_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 6 | 6 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Timeout Specification

## Scenarios

### process_run_timeout

#### completes fast commands successfully

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val (stdout, stderr, code) = process_run_timeout("echo", ["hello"], 5000)
expect(code).to_equal(0)
expect(stdout.trim()).to_contain("hello")
```

</details>

#### uses default timeout when timeout_ms <= 0

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val (stdout, stderr, code) = process_run_timeout("echo", ["test"], 0)
expect(code).to_equal(0)
expect(stdout.trim()).to_contain("test")
```

</details>

#### captures stdout correctly

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val (stdout, stderr, code) = process_run_timeout("echo", ["output test"], 5000)
expect(code).to_equal(0)
expect(stdout).to_contain("output")
```

</details>

#### returns the child's non-zero exit code promptly

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val (stdout, stderr, code) = process_run_timeout("sh", ["-c", "exit 7"], 5000)
expect(code).to_equal(7)
```

</details>

#### returns a timeout marker (not an indefinite block) when the child never exits

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val (stdout, stderr, code) = process_run_timeout("sleep", ["5"], 200)
expect(code).to_equal(-1)
expect(stderr).to_contain("TIMEOUT")
```

</details>

#### does not block on an orphaned grandchild holding output open (native-build worker hang regression)

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val t0 = current_time_ms()
val (stdout, stderr, code) = process_run_timeout("sh", ["-c", "(sleep 5 &) ; echo done; exit 0"], 5000)
val elapsed_ms = current_time_ms() - t0
expect(code).to_equal(0)
expect(stdout.trim()).to_contain("done")
expect(elapsed_ms).to_be_less_than(3000)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/unit/app/io/timeout_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- process_run_timeout

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 6 |
| Active scenarios | 6 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
