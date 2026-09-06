# Bare Bool Types Spec — Semantic Alias Pattern and Lint Level

> Tests the semantic alias pattern (D-4), predicate naming convention (D-1 spirit), and lint level for `bare_bool`:

<!-- sdn-diagram:id=bare_bool_types_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=bare_bool_types_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

bare_bool_types_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=bare_bool_types_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 8 | 8 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Bare Bool Types Spec — Semantic Alias Pattern and Lint Level

Tests the semantic alias pattern (D-4), predicate naming convention (D-1 spirit), and lint level for `bare_bool`:

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | fix-bare-bool-suppressions |
| Category | Tooling |
| Difficulty | 2/5 |
| Status | In Progress |
| Requirements | N/A |
| Plan | N/A |
| Design | N/A |
| Research | N/A |
| Source | `test/03_system/quality/code_quality/bare_bool_types_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests the semantic alias pattern (D-4), predicate naming convention (D-1 spirit),
and lint level for `bare_bool`:

- Group 1: `build_default_levels` returns `"warn"` for `bare_bool` (not deny).
- Group 2: `type Enabled = bool` transparent alias round-trips correctly (D-4 pattern).
- Group 3: Predicate-prefix functions with non-bool params returning bool are
  semantically correct and match the D-1 spirit.

## Scenarios

### bare_bool lint — default level

#### AC-1a: build_default_levels returns warn for bare_bool

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = rt_file_read_text("src/compiler/90.tools/lint/main_part1.spl")
expect(source.contains("levels[\"bare_bool\"] = \"warn\"")).to_equal(true)
```

</details>

### bare_bool types — transparent alias pattern

#### AC-2a: transparent bool alias equals underlying bool true

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
type Enabled = bool
val flag: Enabled = true
expect(flag).to_equal(true)
```

</details>

#### AC-2b: transparent bool alias equals underlying bool false

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
type Deleted = bool
val flag: Deleted = false
expect(flag).to_equal(false)
```

</details>

#### AC-2c: transparent bool alias can be negated like a bool

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
type Active = bool
val a: Active = true
val b = not a
expect(b).to_equal(false)
```

</details>

### bare_bool types — predicate prefix convention

#### AC-3a: is_* fn with non-bool param can return bool

1. fn is above threshold
   - Expected: is_above_threshold(150) is true
   - Expected: is_above_threshold(50) is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
fn is_above_threshold(value: i64) -> bool:
    value > 100
expect(is_above_threshold(150)).to_equal(true)
expect(is_above_threshold(50)).to_equal(false)
```

</details>

#### AC-3b: has_* fn with non-bool param can return bool

1. fn has content
2. s len
   - Expected: has_content("hello") is true
   - Expected: has_content("") is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
fn has_content(s: text) -> bool:
    s.len() > 0
expect(has_content("hello")).to_equal(true)
expect(has_content("")).to_equal(false)
```

</details>

#### AC-3c: can_* fn with no params can return bool

1. fn can proceed
   - Expected: can_proceed() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
fn can_proceed() -> bool:
    true
expect(can_proceed()).to_equal(true)
```

</details>

#### AC-3d: should_* fn with non-bool param can return bool

1. fn should retry
   - Expected: should_retry(1) is true
   - Expected: should_retry(5) is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
fn should_retry(attempts: i64) -> bool:
    attempts < 3
expect(should_retry(1)).to_equal(true)
expect(should_retry(5)).to_equal(false)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 8 |
| Active scenarios | 8 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
