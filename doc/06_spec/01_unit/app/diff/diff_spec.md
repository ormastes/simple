# Diff Unit Tests

> 1. check

<!-- sdn-diagram:id=diff_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=diff_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

diff_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=diff_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 19 | 19 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Diff Unit Tests

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #APP-DIFF-001 |
| Category | App \| Diff |
| Status | Implemented |
| Source | `test/01_unit/app/diff/diff_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Scenarios

### Line Diff

#### identical files

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val changes = 0
check(changes == 0)
```

</details>

#### single line addition

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val additions = 1
check(additions == 1)
```

</details>

#### single line deletion

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val deletions = 1
check(deletions == 1)
```

</details>

#### single line modification

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val modifications = 1
check(modifications == 1)
```

</details>

#### multiple changes

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val additions = 3
val deletions = 2
val total = additions + deletions
check(total == 5)
```

</details>

### Diff Output Format

#### unified diff format

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val format = "unified"
check(format == "unified")
```

</details>

#### context diff format

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val format = "context"
check(format == "context")
```

</details>

#### side-by-side format

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val format = "side-by-side"
check(format == "side-by-side")
```

</details>

#### stat format

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val format = "stat"
check(format == "stat")
```

</details>

### Diff Hunk

#### hunk has start line

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val start = 10
check(start > 0)
```

</details>

#### hunk has line count

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val count = 5
check(count > 0)
```

</details>

#### hunk has context lines

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val context = 3
check(context >= 0)
```

</details>

#### adjacent hunks merged

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val merged = true
check(merged)
```

</details>

### AST Diff

#### function added

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val change = "add_function"
check(change == "add_function")
```

</details>

#### function removed

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val change = "remove_function"
check(change == "remove_function")
```

</details>

#### function signature changed

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val change = "change_signature"
check(change == "change_signature")
```

</details>

#### function body changed

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val change = "change_body"
check(change == "change_body")
```

</details>

#### class field added

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val change = "add_field"
check(change == "add_field")
```

</details>

#### import added

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val change = "add_import"
check(change == "add_import")
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 19 |
| Active scenarios | 19 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
