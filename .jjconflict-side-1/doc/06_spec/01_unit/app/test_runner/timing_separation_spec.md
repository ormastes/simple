# Timing Separation Specification

> <details>

<!-- sdn-diagram:id=timing_separation_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=timing_separation_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

timing_separation_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=timing_separation_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 5 | 5 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Timing Separation Specification

## Scenarios

### TestFileResult setup_ms

#### has setup_ms field defaulting to 0

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(test_setup_ms_default()).to_equal(true)
```

</details>

#### can hold non-zero setup_ms

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(test_setup_ms_nonzero()).to_equal(true)
```

</details>

#### setup_ms is independent of duration_ms

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(test_setup_ms_independent()).to_equal(true)
```

</details>

### TestRunResult total_setup_ms

#### has total_setup_ms field

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(test_run_result_setup_ms()).to_equal(true)
```

</details>

#### defaults to 0

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(test_run_result_setup_ms_zero()).to_equal(true)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/01_unit/app/test_runner/timing_separation_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- TestFileResult setup_ms
- TestRunResult total_setup_ms

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 5 |
| Active scenarios | 5 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
