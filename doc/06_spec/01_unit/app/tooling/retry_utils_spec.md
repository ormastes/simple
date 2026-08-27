# Retry Utils Specification

> 1. expect  retry delay ms

<!-- sdn-diagram:id=retry_utils_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=retry_utils_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

retry_utils_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=retry_utils_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 4 | 4 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Retry Utils Specification

## Scenarios

### RetryUtils

#### computes exponential delay

1. expect  retry delay ms
2. expect  retry delay ms


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect _retry_delay_ms(0, 25, 1000) == 25
expect _retry_delay_ms(3, 25, 1000) == 200
```

</details>

#### caps exponential delay

1. expect  retry delay ms


<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect _retry_delay_ms(8, 25, 500) == 500
```

</details>

#### retries transient statuses

1. expect  should retry
2. expect  should retry


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect _should_retry(1, 3, "timeout") == true
expect _should_retry(1, 3, "temporary") == true
```

</details>

#### stops on permanent status or exhausted attempts

1. expect  should retry
2. expect  should retry


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect _should_retry(1, 3, "permanent") == false
expect _should_retry(3, 3, "timeout") == false
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/01_unit/app/tooling/retry_utils_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- RetryUtils

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 4 |
| Active scenarios | 4 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
