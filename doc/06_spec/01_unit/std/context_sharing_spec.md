# Context Sharing Specification

> 1. expect get let

<!-- sdn-diagram:id=context_sharing_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=context_sharing_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

context_sharing_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=context_sharing_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 14 | 14 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Context Sharing Specification

## Scenarios

### Context Sharing (context_def)

### basic context_def usage

#### provides counter value

1. expect get let


<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect get_let(:counter) == 0
```

</details>

#### provides increment value

1. expect get let


<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect get_let(:increment) == 1
```

</details>

### list context

#### provides items

1. expect len


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val items = get_let(:items)
expect len(items) == 3
```

</details>

#### provides empty list

1. expect len


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val empty = get_let(:empty_list)
expect len(empty) == 0
```

</details>

#### items are accessible

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val items = get_let(:items)
expect items[0] == 1
```

</details>

### string context

#### provides greeting

1. expect get let


<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect get_let(:greeting) == "hello"
```

</details>

#### provides name

1. expect get let


<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect get_let(:name) == "world"
```

</details>

### boolean context

#### provides true flag

1. expect get let


<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect get_let(:flag_true) == true
```

</details>

#### provides false flag

1. expect get let


<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect get_let(:flag_false) == false
```

</details>

### reusing contexts

#### works first time

1. expect get let


<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect get_let(:counter) == 0
```

</details>

#### works second time

1. expect get let


<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect get_let(:counter) == 0
```

</details>

### nested contexts with context_def

#### outer has items

1. expect len


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val items = get_let(:items)
expect len(items) == 3
```

</details>

#### inner context

#### inner has extra

1. expect get let


<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect get_let(:extra) == 99
```

</details>

#### inner still has outer items

1. expect len


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val items = get_let(:items)
expect len(items) == 3
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/std/context_sharing_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- Context Sharing (context_def)
- basic context_def usage
- list context
- string context
- boolean context
- reusing contexts
- nested contexts with context_def

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 14 |
| Active scenarios | 14 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
