# Integration Test Config Specification

> 1. env set

<!-- sdn-diagram:id=integration_test_config_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=integration_test_config_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

integration_test_config_spec -> std
integration_test_config_spec -> app
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=integration_test_config_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 2 | 2 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Integration Test Config Specification

## Scenarios

### Integration Test Config

#### loads live values from config/simple.test.sdn

1. env set
   - Expected: find_config_file().ends_with(CONFIG_FILENAME) is true
   - Expected: config.parallel is false
   - Expected: config.timeout_seconds equals `120`
   - Expected: config.cpu_threshold equals `70.0`
   - Expected: config.memory_threshold equals `70.0`
   - Expected: config.throttle_enabled is true
   - Expected: config.run_spec_tests is true
   - Expected: config.run_sdoctests is true
   - Expected: config.run_slow_tests is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
env_set("CI", "")
val config = TestConfig.load()

expect(find_config_file().ends_with(CONFIG_FILENAME)).to_equal(true)
expect(config.parallel).to_equal(false)
expect(config.timeout_seconds).to_equal(120)
expect(config.cpu_threshold).to_equal(70.0)
expect(config.memory_threshold).to_equal(70.0)
expect(config.throttle_enabled).to_equal(true)
expect(config.run_spec_tests).to_equal(true)
expect(config.run_sdoctests).to_equal(true)
expect(config.run_slow_tests).to_equal(false)
```

</details>

#### applies ci overrides after loading file config

1. env set
   - Expected: config.ci_mode is true
   - Expected: config.run_slow_tests is true
   - Expected: config.fail_fast is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
env_set("CI", "true")
val config = TestConfig.load()

expect(config.ci_mode).to_equal(true)
expect(config.run_slow_tests).to_equal(true)
expect(config.fail_fast).to_equal(false)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/01_unit/app/test_runner_new/integration_test_config_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- Integration Test Config

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 2 |
| Active scenarios | 2 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
