# Env Specification

> <details>

<!-- sdn-diagram:id=env_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=env_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

env_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=env_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 3 | 3 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Env Specification

## Scenarios

### env tool

#### environment listing

#### formats key=value pairs

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val key = "HOME"
val value = "/root"
val formatted = "{key}={value}"
expect(formatted).to_equal("HOME=/root")
```

</details>

#### variable lookup

#### finds existing variable

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val env: [(text, text)] = [("PATH", "/bin"), ("HOME", "/root")]
var found = ""
for pair in env:
    if pair.0 == "HOME":
        found = pair.1
expect(found).to_equal("/root")
```

</details>

#### returns empty for missing variable

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val env: [(text, text)] = [("PATH", "/bin")]
var found = ""
for pair in env:
    if pair.0 == "MISSING":
        found = pair.1
expect(found).to_equal("")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/01_unit/tools/shell/env_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- env tool

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 3 |
| Active scenarios | 3 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
