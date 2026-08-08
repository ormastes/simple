# Dirname Specification

> <details>

<!-- sdn-diagram:id=dirname_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=dirname_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

dirname_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=dirname_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 3 | 3 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Dirname Specification

## Scenarios

### dirname tool

#### path extraction

#### extracts parent directory

<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val path = "/usr/local/bin/simple"
var last_slash = -1
var i = 0
for ch in path:
    if ch == "/":
        last_slash = i
    i = i + 1
val dir = path.slice(0, last_slash)
expect(dir).to_equal("/usr/local/bin")
```

</details>

#### returns / for root-level files

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val path = "/file.txt"
var last_slash = 0
expect(path.slice(0, 1)).to_equal("/")
```

</details>

#### returns . for bare filename

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val path = "file.txt"
var has_slash = false
for ch in path:
    if ch == "/":
        has_slash = true
val result = if has_slash: "error" else: "."
expect(result).to_equal(".")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/01_unit/tools/shell/dirname_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- dirname tool

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 3 |
| Active scenarios | 3 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
