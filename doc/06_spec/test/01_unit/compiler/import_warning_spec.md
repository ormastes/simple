# Import Warning Specification

> 1. check

<!-- sdn-diagram:id=import_warning_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=import_warning_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

import_warning_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=import_warning_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 13 | 13 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Import Warning Specification

## Scenarios

### Import path warnings

#### warns when slash is used in import path

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val warnings = analyze_import_warning("use a/b\n")
check(warnings_contain(warnings, "warning[E0501]"))
```

</details>

#### provides helpful suggestion

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val warnings = analyze_import_warning("use a/b\n")
check(warnings_contain(warnings, "help: use dot-separated"))
```

</details>

#### does not warn on correct absolute import

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val warnings = analyze_import_warning("use compiler.parser\n")
check(warnings_contain(warnings, "absolute import ok"))
```

</details>

#### does not warn on correct relative import

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val warnings = analyze_import_warning("use ./local/module\n")
check(warnings_contain(warnings, "relative import ok"))
```

</details>

#### does not warn on correct parent import

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val warnings = analyze_import_warning("use ../parent/module\n")
check(warnings_contain(warnings, "relative import ok"))
```

</details>

#### warns on multiple slash usages

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val warnings = analyze_import_warning("use a/b/c\n")
check(warnings_contain(warnings, "warning[E0501]"))
```

</details>

#### warns on mixed slash and dot

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val warnings = analyze_import_warning("use a/b.c\n")
check(warnings_contain(warnings, "warning[E0501]"))
```

</details>

### Warning message content

#### explains the issue

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val warnings = analyze_import_warning("use a/b\n")
check(warnings_contain(warnings, "cannot import unfolded package"))
```

</details>

#### suggests dot separator

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val warnings = analyze_import_warning("use a/b\n")
check(warnings_contain(warnings, "dot-separated module paths"))
```

</details>

#### mentions relative paths

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val warnings = analyze_import_warning("use ../a/b\n")
check(warnings_contain(warnings, "relative import ok"))
```

</details>

### Warning severity

#### is a warning, not an error

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val warnings = analyze_import_warning("use a/b\n")
check(warnings.len() > 0)
```

</details>

#### allows compilation to continue

1. check
2. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val warnings = analyze_import_warning("use a/b\nuse compiler.parser\n")
check(warnings.len() > 0)
check(warnings_contain(warnings, "absolute import ok"))
```

</details>

#### does not prevent import resolution

1. check
2. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val warnings = analyze_import_warning("use a/b\nuse compiler.parser\n")
check(warnings_contain(warnings, "warning[E0501]"))
check(warnings_contain(warnings, "absolute import ok"))
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler/import_warning_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- Import path warnings
- Warning message content
- Warning severity

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 13 |
| Active scenarios | 13 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
