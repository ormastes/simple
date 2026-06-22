# Test Config Float Fallback Specification

> <details>

<!-- sdn-diagram:id=test_config_float_fallback_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=test_config_float_fallback_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

test_config_float_fallback_spec -> app
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=test_config_float_fallback_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 1 | 1 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Test Config Float Fallback Specification

## Scenarios

### TestConfig float parsing

#### keeps malformed float thresholds from crashing config parsing

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val parsed = parse_test_config_content(TestConfig.defaults(), "test:\n  cpu_threshold: nope\n  memory_threshold: .\n")
expect(parsed.cpu_threshold >= 0.0).to_equal(true)
expect(parsed.memory_threshold >= 0.0).to_equal(true)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/01_unit/app/test_runner_new/test_config_float_fallback_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- TestConfig float parsing

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 1 |
| Active scenarios | 1 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
