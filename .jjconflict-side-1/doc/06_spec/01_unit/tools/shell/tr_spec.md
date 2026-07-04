# Tr Specification

> <details>

<!-- sdn-diagram:id=tr_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=tr_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

tr_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=tr_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 3 | 3 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Tr Specification

## Scenarios

### tr tool

#### character translation

#### translates characters

<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val input = "hello"
var output = ""
for ch in input:
    if ch == "l":
        output = "{output}r"
    else:
        output = "{output}{ch}"
expect(output).to_equal("herro")
```

</details>

#### character deletion

#### deletes specified characters

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val input = "hello world"
var output = ""
for ch in input:
    if ch != "l":
        output = "{output}{ch}"
expect(output).to_equal("heo word")
```

</details>

#### squeeze

#### squeezes repeated characters

<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val input = "aabbcc"
var output = ""
var prev = ""
for ch in input:
    if ch != prev:
        output = "{output}{ch}"
    prev = ch
expect(output).to_equal("abc")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/01_unit/tools/shell/tr_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- tr tool

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 3 |
| Active scenarios | 3 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
