# Import Syntax Specification

> 1. expect result len

<!-- sdn-diagram:id=import_syntax_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=import_syntax_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

import_syntax_spec -> app
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=import_syntax_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 5 | 5 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Import Syntax Specification

## Scenarios

### Import Syntax for mod.spl Files

#### Curly braces syntax: use app.io.{...}

#### imports env_get with curly braces

1. expect result len


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = env_get("PATH")
expect result.len() > 0
```

</details>

#### imports env_set with curly braces

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = env_set("TEST_VAR_CURLY", "test")
expect result == true
```

</details>

#### imports shell with curly braces

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = shell("echo test")
expect result.exit_code == 0
```

</details>

#### Parentheses syntax: use app.io.mod (...)

#### imports file_exists with parentheses

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = file_exists("test/integration/import_syntax_spec.spl")
expect result == true
```

</details>

#### imports cwd with parentheses

1. expect result len


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = cwd()
expect result.len() > 0
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/02_integration/compiler/import_syntax_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- Import Syntax for mod.spl Files

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 5 |
| Active scenarios | 5 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
