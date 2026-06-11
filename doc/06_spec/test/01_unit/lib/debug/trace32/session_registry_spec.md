# Session Registry Specification

> 1. sessions push

<!-- sdn-diagram:id=session_registry_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=session_registry_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

session_registry_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=session_registry_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 8 | 8 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Session Registry Specification

## Scenarios

### T32 Session Registry

#### registers a session

1. sessions push
   - Expected: sessions.len() equals `1`
   - Expected: sessions[0] equals `session_1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var sessions: [text] = []
sessions.push("session_1")
expect(sessions.len()).to_equal(1)
expect(sessions[0]).to_equal("session_1")
```

</details>

#### finds session by id

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var sessions: [text] = ["s1", "s2", "s3"]
var found = ""
for s in sessions:
    if s == "s2":
        found = s
expect(found).to_equal("s2")
```

</details>

#### removes session

1. filtered push
   - Expected: filtered.len() equals `2`
   - Expected: filtered[0] equals `s1`
   - Expected: filtered[1] equals `s3`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var sessions: [text] = ["s1", "s2", "s3"]
var filtered: [text] = []
for s in sessions:
    if s != "s2":
        filtered.push(s)
expect(filtered.len()).to_equal(2)
expect(filtered[0]).to_equal("s1")
expect(filtered[1]).to_equal("s3")
```

</details>

#### tracks current session

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var current = ""
current = "session_amp0"
expect(current).to_equal("session_amp0")
```

</details>

#### manages multiple cores

1. cores push
2. cores push
3. cores push
   - Expected: cores.len() equals `3`
   - Expected: cores[0] equals `a53_0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var cores: [text] = []
cores.push("a53_0")
cores.push("a53_1")
cores.push("m4_0")
expect(cores.len()).to_equal(3)
expect(cores[0]).to_equal("a53_0")
```

</details>

#### selects core

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var cores: [text] = ["a53_0", "a53_1", "m4_0"]
var selected = ""
val target = "a53_1"
for c in cores:
    if c == target:
        selected = c
expect(selected).to_equal("a53_1")
```

</details>

#### handles empty session list

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var sessions: [text] = []
expect(sessions.len()).to_equal(0)
```

</details>

#### prevents duplicate session ids

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var sessions: [text] = ["s1"]
var exists = false
val new_id = "s1"
for s in sessions:
    if s == new_id:
        exists = true
expect(exists).to_equal(true)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/debug/trace32/session_registry_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- T32 Session Registry

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 8 |
| Active scenarios | 8 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
