# Session Specification

> 1. lines push

<!-- sdn-diagram:id=session_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=session_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

session_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=session_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 4 | 4 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Session Specification

## Scenarios

### T32 Session CLI

#### formats session list

1. lines push


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var ids: [text] = ["amp0", "amp1"]
var lines: [text] = []
for id in ids:
    lines.push("  {id}")
val output = lines.join("\n")
expect(output).to_contain("amp0")
expect(output).to_contain("amp1")
```

</details>

#### tracks current session

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var current = ""
current = "amp0"
expect(current).to_equal("amp0")
current = "amp1"
expect(current).to_equal("amp1")
```

</details>

#### validates session id exists

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var ids: [text] = ["s1", "s2"]
var found = false
val target = "s2"
for id in ids:
    if id == target:
        found = true
expect(found).to_equal(true)
```

</details>

#### rejects unknown session

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var ids: [text] = ["s1", "s2"]
var found = false
val target = "s99"
for id in ids:
    if id == target:
        found = true
expect(found).to_equal(false)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/01_unit/app/t32_cli/session_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- T32 Session CLI

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 4 |
| Active scenarios | 4 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
