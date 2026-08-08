# Threshold Parser Specification

> <details>

<!-- sdn-diagram:id=threshold_parser_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=threshold_parser_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

threshold_parser_spec -> std
threshold_parser_spec -> doc_coverage
threshold_parser_spec -> app
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=threshold_parser_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 23 | 23 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Threshold Parser Specification

## Scenarios

### parse_threshold_config default behavior

#### returns default config when file does not exist

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val config = parse_threshold_config("/nonexistent/path/config.sdn")

val default_threshold = config.default_threshold
expect(default_threshold).to_equal(70)
```

</details>

#### returns default values for non-existent file

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val config = parse_threshold_config("/tmp/missing_config.sdn")

val enforce = config.enforce
val fail_on_below = config.fail_on_below

expect(enforce).to_equal(false)
expect(fail_on_below).to_equal(false)
```

</details>

### parse_threshold_config from test fixture

#### parses default_threshold value

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val config_path = fixture_path("test_config.sdn")
val config = parse_threshold_config(config_path)

val default_threshold = config.default_threshold
expect(default_threshold).to_equal(70)
```

</details>

#### parses enforce flag

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val config_path = fixture_path("test_config.sdn")
val config = parse_threshold_config(config_path)

val enforce = config.enforce
expect(enforce).to_equal(true)
```

</details>

#### parses fail_on_below_threshold flag

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val config_path = fixture_path("test_config.sdn")
val config = parse_threshold_config(config_path)

val fail_on_below = config.fail_on_below
expect(fail_on_below).to_equal(false)
```

</details>

#### parses scope thresholds

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val config_path = fixture_path("test_config.sdn")
val config = parse_threshold_config(config_path)

val scope_count = config.scope_names.len()
val has_scopes = scope_count > 0

expect(has_scopes).to_equal(true)
```

</details>

#### parses std scope threshold correctly

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val config_path = fixture_path("test_config.sdn")
val config = parse_threshold_config(config_path)

val std_threshold = threshold_config_get(config, "src/std/")
expect(std_threshold).to_equal(90)
```

</details>

#### parses core scope threshold correctly

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val config_path = fixture_path("test_config.sdn")
val config = parse_threshold_config(config_path)

val core_threshold = threshold_config_get(config, "src/core/")
expect(core_threshold).to_equal(75)
```

</details>

#### parses lib scope threshold correctly

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val config_path = fixture_path("test_config.sdn")
val config = parse_threshold_config(config_path)

val lib_threshold = threshold_config_get(config, "src/lib/")
expect(lib_threshold).to_equal(80)
```

</details>

#### parses app scope threshold correctly

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val config_path = fixture_path("test_config.sdn")
val config = parse_threshold_config(config_path)

val app_threshold = threshold_config_get(config, "src/app/")
expect(app_threshold).to_equal(50)
```

</details>

#### parses compiler scope threshold correctly

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val config_path = fixture_path("test_config.sdn")
val config = parse_threshold_config(config_path)

val compiler_threshold = threshold_config_get(config, "src/compiler/")
expect(compiler_threshold).to_equal(60)
```

</details>

#### parses exclusion patterns

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val config_path = fixture_path("test_config.sdn")
val config = parse_threshold_config(config_path)

val exclusion_count = config.exclusions.len()
val has_exclusions = exclusion_count > 0

expect(has_exclusions).to_equal(true)
```

</details>

#### includes test exclusion pattern

<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val config_path = fixture_path("test_config.sdn")
val config = parse_threshold_config(config_path)

var has_test_pattern = false
for pattern in config.exclusions:
    if pattern.contains("test"):
        has_test_pattern = true

expect(has_test_pattern).to_equal(true)
```

</details>

#### includes deprecated exclusion pattern

<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val config_path = fixture_path("test_config.sdn")
val config = parse_threshold_config(config_path)

var has_deprecated_pattern = false
for pattern in config.exclusions:
    if pattern.contains("deprecated"):
        has_deprecated_pattern = true

expect(has_deprecated_pattern).to_equal(true)
```

</details>

### threshold_config_get lookup

#### returns default threshold for unknown scope

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val config_path = fixture_path("test_config.sdn")
val config = parse_threshold_config(config_path)

val unknown_threshold = threshold_config_get(config, "unknown/path/")
val default_value = config.default_threshold

expect(unknown_threshold).to_equal(default_value)
```

</details>

#### matches scope prefix correctly

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val config_path = fixture_path("test_config.sdn")
val config = parse_threshold_config(config_path)

val file_threshold = threshold_config_get(config, "src/std/string.spl")
expect(file_threshold).to_equal(90)
```

</details>

#### handles multiple scope lookups

<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val config_path = fixture_path("test_config.sdn")
val config = parse_threshold_config(config_path)

val std_val = threshold_config_get(config, "src/std/test.spl")
val core_val = threshold_config_get(config, "src/core/test.spl")
val lib_val = threshold_config_get(config, "src/lib/test.spl")

val std_correct = std_val == 90
val core_correct = core_val == 75
val lib_correct = lib_val == 80

expect(std_correct).to_equal(true)
expect(core_correct).to_equal(true)
expect(lib_correct).to_equal(true)
```

</details>

### parse_threshold_config edge cases

#### handles empty scope names array

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val config = parse_threshold_config("/nonexistent/config.sdn")

val scope_count = config.scope_names.len()
expect(scope_count).to_equal(0)
```

</details>

#### handles empty exclusions array

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val config = parse_threshold_config("/nonexistent/config.sdn")

val exclusion_count = config.exclusions.len()
expect(exclusion_count).to_equal(0)
```

</details>

#### default threshold is reasonable value

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val config = parse_threshold_config("/nonexistent/config.sdn")

val threshold = config.default_threshold
val is_reasonable = threshold >= 0 and threshold <= 100

expect(is_reasonable).to_equal(true)
```

</details>

### parse_threshold_config integration

#### parses complete config file correctly

<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val config_path = fixture_path("test_config.sdn")
val config = parse_threshold_config(config_path)

val has_default = config.default_threshold > 0
val has_scopes = config.scope_names.len() > 0
val has_exclusions = config.exclusions.len() > 0

expect(has_default).to_equal(true)
expect(has_scopes).to_equal(true)
expect(has_exclusions).to_equal(true)
```

</details>

#### all scope thresholds are valid percentages

<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val config_path = fixture_path("test_config.sdn")
val config = parse_threshold_config(config_path)

var all_valid = true
var i = 0
while i < config.scope_values.len():
    val threshold = config.scope_values[i]
    if threshold < 0 or threshold > 100:
        all_valid = false
    i = i + 1

expect(all_valid).to_equal(true)
```

</details>

#### scope names and values have matching lengths

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val config_path = fixture_path("test_config.sdn")
val config = parse_threshold_config(config_path)

val names_len = config.scope_names.len()
val values_len = config.scope_values.len()

expect(names_len).to_equal(values_len)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/01_unit/app/doc_coverage/threshold_parser_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- parse_threshold_config default behavior
- parse_threshold_config from test fixture
- threshold_config_get lookup
- parse_threshold_config edge cases
- parse_threshold_config integration

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 23 |
| Active scenarios | 23 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
