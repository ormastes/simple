# Skip-Native Mode Tests

> Tests that skip native compilation via `skip-marker-removed_mode: native`, running only in interpreter and SMF modes.

<!-- sdn-diagram:id=skip_native_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=skip_native_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

skip_native_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=skip_native_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 1 | 1 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Skip-Native Mode Tests

Tests that skip native compilation via `skip-marker-removed_mode: native`, running only in interpreter and SMF modes.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Testing Framework |
| Status | Active |
| Source | `test/03_system/feature/mode_filter/skip_native_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests that skip native compilation via `skip-marker-removed_mode: native`, running only in interpreter and SMF modes.

## Scenarios

### Non-native tests

#### works in interpreted modes

- assert true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var interpreted_body_ran = false
interpreted_body_ran = true
assert_true(interpreted_body_ran)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 1 |
| Active scenarios | 1 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
