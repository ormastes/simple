# String Utils Specification

> 1. expect raw trim

<!-- sdn-diagram:id=string_utils_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=string_utils_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

string_utils_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=string_utils_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 4 | 4 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# String Utils Specification

## Scenarios

### String Utils

#### trims surrounding whitespace

1. expect raw trim


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val raw = "  build report  "
expect raw.trim() == "build report"
```

</details>

#### detects expected prefixes and suffixes

1. expect path starts with
2. expect path ends with


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val path = "src/app/tooling/main.spl"
expect path.starts_with("src/app") == true
expect path.ends_with(".spl") == true
```

</details>

#### splits path segments

1. expect parts len


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val parts = "src/app/tooling".split("/")
expect parts.len() == 3
expect parts[0] == "src"
expect parts[2] == "tooling"
```

</details>

#### normalizes separators with replace

1. expect name replace


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val name = "skip test todo"
expect name.replace(" ", "_") == "skip_test_todo"
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/01_unit/app/tooling/string_utils_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- String Utils

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 4 |
| Active scenarios | 4 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
