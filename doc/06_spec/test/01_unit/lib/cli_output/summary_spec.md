# Summary Specification

> <details>

<!-- sdn-diagram:id=summary_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=summary_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

summary_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=summary_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 12 | 12 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Summary Specification

## Scenarios

### cli_output.summary

#### format_summary

#### should format all-pass summary

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = format_summary(47, 0, 0, 0, 1340)
expect(result).to_contain("47 passed")
expect(result).to_contain("1.34s")
```

</details>

#### should format summary with failures

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = format_summary(45, 2, 0, 0, 1340)
expect(result).to_contain("45 passed")
expect(result).to_contain("2 failed")
```

</details>

#### should format summary with warnings

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = format_summary(45, 2, 3, 0, 1340)
expect(result).to_contain("45 passed")
expect(result).to_contain("2 failed")
expect(result).to_contain("3 warnings")
```

</details>

#### should include duration in summary

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = format_summary(10, 0, 0, 0, 500)
expect(result).to_contain("500ms")
```

</details>

#### format_duration

#### should format sub-second durations

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = format_duration(450)
expect(result).to_equal("450ms")
```

</details>

#### should format seconds with centiseconds

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = format_duration(1340)
expect(result).to_equal("1.34s")
```

</details>

#### should format minutes and seconds

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = format_duration(135000)
expect(result).to_equal("2m 15s")
```

</details>

#### should format exact minutes

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = format_duration(120000)
expect(result).to_equal("2m")
```

</details>

#### print helpers

#### should print error without crashing

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = print_error_now("test error message")
expect(result).to_equal("error: test error message")
```

</details>

#### should suppress warning when not strict

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = print_warning_now("test warning", false)
expect(result).to_equal("")
```

</details>

#### should print warning when strict

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = print_warning_now("test warning", true)
expect(result).to_equal("warning: test warning")
```

</details>

#### should print log hint without crashing

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = print_log_hint("test")
expect(result).to_equal("Full log: build/log/test/latest.log")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/cli_output/summary_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- cli_output.summary

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 12 |
| Active scenarios | 12 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
