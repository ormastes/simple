# Test Config Specification

> <details>

<!-- sdn-diagram:id=test_config_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=test_config_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

test_config_spec -> app
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=test_config_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 12 | 12 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Test Config Specification

## Scenarios

### TestConfig

#### default configuration

#### loads default values when config file not found

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val config = TestConfig.defaults()
expect(config.timeout_seconds).to_equal(60)
expect(config.memory_limit_mb).to_equal(512)
expect(config.cpu_limit_seconds).to_equal(30)
```

</details>

#### test mode flags

#### defaults to running both spec tests and sdoctests

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val config = TestConfig.defaults()
expect(config.run_spec_tests).to_equal(true)
expect(config.run_sdoctests).to_equal(true)
```

</details>

#### defaults to excluding slow tests

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val config = TestConfig.defaults()
expect(config.run_slow_tests == false).to_equal(true)
```

</details>

#### CI mode

#### detects CI mode from environment variable

1. env set
   - Expected: config.ci_mode is true
2. env set


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val original_ci = env_get("CI") ?? ""
env_set("CI", "true")
val config = TestConfig.load()
expect(config.ci_mode).to_equal(true)
if original_ci != "":
    env_set("CI", original_ci)
```

</details>

#### includes slow tests when CI mode is active

1. env set
   - Expected: config.run_slow_tests is true
2. env set


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val original_ci = env_get("CI") ?? ""
env_set("CI", "true")
val config = TestConfig.load()
expect(config.run_slow_tests).to_equal(true)
if original_ci != "":
    env_set("CI", original_ci)
```

</details>

#### disables fail_fast in CI mode

1. env set
   - Expected: config.fail_fast == false is true
2. env set


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val original_ci = env_get("CI") ?? ""
env_set("CI", "true")
val config = TestConfig.load()
expect(config.fail_fast == false).to_equal(true)
if original_ci != "":
    env_set("CI", original_ci)
```

</details>

### TestConfig parsing

#### boolean fields

#### parses run_spec_tests from config file

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val config = TestConfig.defaults()
# run_spec_tests defaults to true - verify the field is accessible
expect(config.run_spec_tests).to_equal(true)
```

</details>

#### parses run_sdoctests from config file

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val config = TestConfig.defaults()
# run_sdoctests defaults to true - verify the field is accessible
expect(config.run_sdoctests).to_equal(true)
```

</details>

#### parses run_slow_tests from config file

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val config = TestConfig.defaults()
# run_slow_tests defaults to false - verify the field is accessible
expect(config.run_slow_tests == false).to_equal(true)
```

</details>

#### multi-level config search

#### finds config in current directory

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val path = find_config_file()
# Either found config/simple.test.sdn or returned empty string
expect(path == "" or path.contains("simple.test.sdn")).to_equal(true)
```

</details>

#### finds config in parent directory

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val path = find_config_file()
# find_config_file searches current, parent, and grandparent
# result is either empty or a valid config path
expect(path == "" or path.ends_with(CONFIG_FILENAME)).to_equal(true)
```

</details>

#### finds config in grandparent directory

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val path = find_config_file()
# CONFIG_FILENAME constant is "config/simple.test.sdn"
expect(CONFIG_FILENAME).to_equal("config/simple.test.sdn")
# find_config_file returns empty or a path ending in the config filename
expect(path == "" or path.contains("config/simple.test.sdn")).to_equal(true)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/01_unit/app/test_runner_new/test_config_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- TestConfig
- TestConfig parsing

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 12 |
| Active scenarios | 12 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
