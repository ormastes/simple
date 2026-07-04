# Shutdown Specification

> <details>

<!-- sdn-diagram:id=shutdown_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=shutdown_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

shutdown_spec -> app
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=shutdown_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 8 | 8 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Shutdown Specification

## Scenarios

### exit codes

#### should have distinct exit codes

<details>
<summary>Executable SSpec</summary>

Runnable source: 19 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(EXIT_SUCCESS).to_equal(0)
expect(EXIT_FAILURE).to_equal(1)
expect(EXIT_RESOURCE_SHUTDOWN).to_equal(42)
expect(EXIT_RECOVERY_FAILED).to_equal(43)

# All codes should be different
val all_different = EXIT_SUCCESS != EXIT_FAILURE
val diff2 = EXIT_SUCCESS != EXIT_RESOURCE_SHUTDOWN
val diff3 = EXIT_SUCCESS != EXIT_RECOVERY_FAILED
val diff4 = EXIT_FAILURE != EXIT_RESOURCE_SHUTDOWN
val diff5 = EXIT_FAILURE != EXIT_RECOVERY_FAILED
val diff6 = EXIT_RESOURCE_SHUTDOWN != EXIT_RECOVERY_FAILED

expect(all_different).to_equal(true)
expect(diff2).to_equal(true)
expect(diff3).to_equal(true)
expect(diff4).to_equal(true)
expect(diff5).to_equal(true)
expect(diff6).to_equal(true)
```

</details>

### shutdown_format_summary

#### should format summary with all fields

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val summary = shutdown_format_summary("cpu", [], 10, 2, 3)

expect(summary.contains("cpu")).to_equal(true)
expect(summary.contains("10")).to_equal(true)
expect(summary.contains("2")).to_equal(true)
expect(summary.contains("3")).to_equal(true)
```

</details>

#### should include reason in summary

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val summary = shutdown_format_summary("memory", [], 0, 0, 0)

expect(summary.contains("memory")).to_equal(true)
```

</details>

#### should format with multiple completed files

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val completed = ["a.spl", "b.spl", "c.spl"]
val summary = shutdown_format_summary("cpu", completed, 5, 1, 2)

expect(summary.contains("3")).to_equal(true)  # 3 completed files
```

</details>

#### should handle empty completed list

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val completed: [text] = []
val summary = shutdown_format_summary("periodic", completed, 0, 0, 0)

expect(summary.contains("0")).to_equal(true)
```

</details>

#### should include passed count

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val summary = shutdown_format_summary("test", [], 42, 0, 0)

expect(summary.contains("42")).to_equal(true)
```

</details>

#### should include failed count

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val summary = shutdown_format_summary("test", [], 0, 7, 0)

expect(summary.contains("7")).to_equal(true)
```

</details>

#### should include skipped count

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val summary = shutdown_format_summary("test", [], 0, 0, 9)

expect(summary.contains("9")).to_equal(true)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/01_unit/app/test_runner_new/shutdown_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- exit codes
- shutdown_format_summary

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 8 |
| Active scenarios | 8 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
