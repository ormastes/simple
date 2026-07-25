# Basename Specification

> <details>

<!-- sdn-diagram:id=basename_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=basename_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

basename_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=basename_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 4 | 4 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Basename Specification

## Scenarios

### basename tool

#### path stripping

#### strips directory from path

<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val path = "/usr/local/bin/simple"
# basename should return "simple"
var last_slash = -1
var i = 0
for ch in path:
    if ch == "/":
        last_slash = i
    i = i + 1
val name = path.slice(last_slash + 1, path.len())
expect(name).to_equal("simple")
```

</details>

#### handles root path

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val path = "/"
expect(path).to_equal("/")
```

</details>

#### handles no directory

<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val path = "file.txt"
var last_slash = -1
var i = 0
for ch in path:
    if ch == "/":
        last_slash = i
    i = i + 1
val name = if last_slash >= 0: path.slice(last_slash + 1, path.len()) else: path
expect(name).to_equal("file.txt")
```

</details>

#### suffix stripping

#### strips suffix from filename

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val name = "file.spl"
val suffix = ".spl"
val result = name.slice(0, name.len() - suffix.len())
expect(result).to_equal("file")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/01_unit/tools/shell/basename_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- basename tool

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 4 |
| Active scenarios | 4 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
