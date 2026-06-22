# Test Runner Resources Specification

> <details>

<!-- sdn-diagram:id=test_runner_resources_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=test_runner_resources_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

test_runner_resources_spec -> std
test_runner_resources_spec -> app
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=test_runner_resources_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 4 | 4 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Test Runner Resources Specification

## Scenarios

### Test Runner Resources

#### builds default, slow, and disabled limits

<details>
<summary>Executable SSpec</summary>

Runnable source: 18 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val default_limits = default_resource_limits()
val slow_limits = resource_limits_for_slow_tests()
val disabled_limits = resource_limits_disabled()

expect(default_limits.cpu_percent_limit).to_equal(200.0)
expect(default_limits.memory_mb_limit).to_equal(512)
expect(default_limits.fd_limit).to_equal(1024)
expect(default_limits.enabled).to_equal(true)

expect(slow_limits.cpu_percent_limit).to_equal(400.0)
expect(slow_limits.memory_mb_limit).to_equal(1024)
expect(slow_limits.fd_limit).to_equal(2048)
expect(slow_limits.enabled).to_equal(true)

expect(disabled_limits.cpu_percent_limit).to_equal(0.0)
expect(disabled_limits.memory_mb_limit).to_equal(0)
expect(disabled_limits.fd_limit).to_equal(0)
expect(disabled_limits.enabled).to_equal(false)
```

</details>

#### formats violation alerts only when violations exist

<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val alert = format_violation_alert("test/example_spec.spl", sample_resource_record("cpu,memory,fds", 1))
val empty = format_violation_alert("test/example_spec.spl", sample_resource_record("", 1))

expect(alert).to_contain("[RESOURCE VIOLATION]")
expect(alert).to_contain("CPU")
expect(alert).to_contain("Memory")
expect(alert).to_contain("File Descriptors")
expect(empty).to_equal("")
```

</details>

#### detects violations and formats metrics

<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val violating = sample_resource_record("cpu", 1)
val clean = sample_resource_record("", 1)
val formatted = format_resource_metrics(violating)

expect(has_violations(violating)).to_equal(true)
expect(has_violations(clean)).to_equal(false)
expect(formatted).to_contain("CPU: 250")
expect(formatted).to_contain("Mem: 1024")
expect(formatted).to_contain("FDs: 42")
```

</details>

#### appends resource information only when samples exist

<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val output = "Test output"
val appended = append_resource_info_to_output("test/example_spec.spl", sample_resource_record("cpu", 3), output)
val untouched = append_resource_info_to_output("test/example_spec.spl", sample_resource_record("", 0), output)

expect(appended).to_contain("Test output")
expect(appended).to_contain("Resource Usage")
expect(appended).to_contain("Resource violations: cpu")
expect(untouched).to_equal(output)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/01_unit/app/test_runner_new/test_runner_resources_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- Test Runner Resources

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 4 |
| Active scenarios | 4 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
