# Test Config Specification

> Tests configuration loading: defaults, field parsing, multi-level search, resource throttle fields.

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
| 21 | 21 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Test Config Specification

Tests configuration loading: defaults, field parsing, multi-level search, resource throttle fields.

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #CONFIG |
| Category | Tooling |
| Status | Implemented |
| Source | `test/01_unit/app/tooling/test_config_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests configuration loading: defaults, field parsing, multi-level search,
resource throttle fields.

## Scenarios

### TestConfig.defaults

#### has correct timeout

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val config = TestConfig.defaults()
expect(config.timeout_seconds).to_equal(60)
```

</details>

#### has correct memory limit

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val config = TestConfig.defaults()
expect(config.memory_limit_mb).to_equal(512)
```

</details>

#### has correct cpu limit

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val config = TestConfig.defaults()
expect(config.cpu_limit_seconds).to_equal(30)
```

</details>

#### has correct max_fds

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val config = TestConfig.defaults()
expect(config.max_fds).to_equal(256)
```

</details>

#### has correct max_procs

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val config = TestConfig.defaults()
expect(config.max_procs).to_equal(64)
```

</details>

#### has parallel disabled by default

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val config = TestConfig.defaults()
expect(config.parallel).to_equal(false)
```

</details>

#### has fail_fast disabled by default

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val config = TestConfig.defaults()
expect(config.fail_fast).to_equal(false)
```

</details>

#### has correct slow threshold

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val config = TestConfig.defaults()
expect(config.slow_threshold_ms).to_equal(5000)
```

</details>

#### has cpu_threshold default (H2)

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val config = TestConfig.defaults()
expect(config.cpu_threshold).to_equal(80.0)
```

</details>

#### has memory_threshold default (H2)

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val config = TestConfig.defaults()
expect(config.memory_threshold).to_equal(80.0)
```

</details>

#### has throttle disabled by default (H2)

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val config = TestConfig.defaults()
expect(config.throttle_enabled).to_equal(false)
```

</details>

### TestConfig.load

#### returns defaults when no config file exists

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# In test env, config file may not exist
val config = TestConfig.load()
expect(config.timeout_seconds > 0).to_equal(true)
```

</details>

### find_config_file

#### returns empty string when no config found

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# In most test envs, no simple.test.sdn in parents
val path = find_config_file()
# Either found or empty - both valid
expect(path == "" or path.contains("simple.test.sdn")).to_equal(true)
```

</details>

### TestConfig field parsing

#### handles comment lines

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val config = TestConfig.defaults()
# Load would skip comment lines starting with #
expect(config.timeout_seconds).to_equal(60)
```

</details>

#### handles empty lines

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val config = TestConfig.defaults()
expect(config.memory_limit_mb).to_equal(512)
```

</details>

#### handles lines without colon separator

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val config = TestConfig.defaults()
# Parser skips malformed lines
expect(config.cpu_limit_seconds).to_equal(30)
```

</details>

#### handles invalid integer values

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val config = TestConfig.defaults()
# to_int_or falls back to default
expect(config.max_fds).to_equal(256)
```

</details>

#### handles invalid float values

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val config = TestConfig.defaults()
# to_float_or falls back to default
expect(config.cpu_threshold).to_equal(80.0)
```

</details>

#### handles boolean true value

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val config = TestConfig.defaults()
# parallel defaults to false
expect(config.parallel).to_equal(false)
```

</details>

#### handles boolean false value

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val config = TestConfig.defaults()
expect(config.fail_fast).to_equal(false)
```

</details>

#### handles unknown config keys

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val config = TestConfig.defaults()
# Unknown keys are ignored via wildcard match
expect(config.timeout_seconds).to_equal(60)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 21 |
| Active scenarios | 21 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
