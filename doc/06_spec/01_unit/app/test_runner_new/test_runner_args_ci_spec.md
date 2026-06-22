# Test Runner Args Ci Specification

> <details>

<!-- sdn-diagram:id=test_runner_args_ci_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=test_runner_args_ci_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

test_runner_args_ci_spec -> std
test_runner_args_ci_spec -> app
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=test_runner_args_ci_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 4 | 4 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Test Runner Args Ci Specification

## Scenarios

### Test Runner Args Ci

#### enables ci mode defaults

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val options = parse_test_args(["--ci"])

expect(options.ci_mode).to_equal(true)
expect(options.run_all).to_equal(true)
expect(options.fail_fast).to_equal(false)
```

</details>

#### keeps other flags when ci mode is enabled

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val options = parse_test_args(["--ci", "--verbose", "test/unit/"])

expect(options.ci_mode).to_equal(true)
expect(options.verbose).to_equal(true)
expect(options.path).to_equal("test/unit/")
```

</details>

#### leaves ci mode disabled by default

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val options = parse_test_args([])

expect(options.ci_mode).to_equal(false)
expect(options.run_all).to_equal(false)
```

</details>

#### preserves sdoctest behavior

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val options = parse_test_args(["--sdoctest"])

expect(options.sdoctest).to_equal(true)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/01_unit/app/test_runner_new/test_runner_args_ci_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- Test Runner Args Ci

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 4 |
| Active scenarios | 4 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
