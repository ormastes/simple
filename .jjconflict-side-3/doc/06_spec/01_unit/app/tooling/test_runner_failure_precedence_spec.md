# Test Runner Failure Precedence Specification

> Tests covering test runner failure precedence.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 4 | 4 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Test Runner Failure Precedence Specification

## Scenarios

### test runner failure precedence

#### keeps a nonzero child exit red after a green summary

<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = make_result_from_output(
    "green_then_crash_spec.spl",
    "1 example, 0 failures",
    "",
    7i32,
    1,
    30
)

expect(result.is_ok()).to_equal(false)
expect(result.failed).to_equal(1)
expect(result.error).to_contain("Process exited with code 7")
```

</details>

#### keeps an ordinary green child green

<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = make_result_from_output(
    "green_spec.spl",
    "1 example, 0 failures",
    "",
    0i32,
    1,
    30
)

expect(result.is_ok()).to_equal(true)
expect(result.failed).to_equal(0)
```

</details>

#### keeps pending-only and mixed active summaries out of pass inflation

<details>
<summary>Executable SSpec</summary>

Runnable source: 29 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val pending_only = make_result_from_output(
    "pending_only_spec.spl",
    "    it unavailable host ... pending\n" +
    "Test Summary:\n  Total:   1\n  Passed:  0\n" +
    "  Failed:  0\n  Pending: 1\n",
    "",
    0i32,
    1,
    30
)
expect(pending_only.passed).to_equal(0)
expect(pending_only.failed).to_equal(0)
expect(pending_only.pending).to_equal(1)
expect(pending_only.error).to_equal("")

val mixed = make_result_from_output(
    "pending_and_active_spec.spl",
    "    it unavailable host ... pending\n" +
    "    it active path ... ok\n" +
    "Test Summary:\n  Total:   2\n  Passed:  1\n" +
    "  Failed:  0\n  Pending: 1\n",
    "",
    0i32,
    1,
    30
)
expect(mixed.passed).to_equal(1)
expect(mixed.failed).to_equal(0)
expect(mixed.pending).to_equal(1)
```

</details>

#### routes daemon-owned nested tests directly

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val client = rt_file_read_text("src/app/test_runner_new/test_runner_client.spl") ?? ""
val daemon = rt_file_read_text("src/app/test_daemon/light_daemon.spl") ?? ""

expect(client).to_contain("env_get(\"SIMPLE_TEST_DAEMON_CHILD\") == \"1\"")
expect(client).to_contain("return run_direct(run)")
expect(daemon).to_contain("env_set(\"SIMPLE_TEST_DAEMON_CHILD\", \"1\")")
expect(daemon).to_contain("env_set(\"SIMPLE_TEST_DAEMON_CHILD\", previous_child_marker)")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/01_unit/app/tooling/test_runner_failure_precedence_spec.spl` |
| Updated | 2026-07-29 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering test runner failure precedence.
- test runner failure precedence

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 4 |
| Active scenarios | 4 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
