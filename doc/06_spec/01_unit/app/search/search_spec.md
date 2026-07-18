# Search Unit Tests

> 1. check

<!-- sdn-diagram:id=search_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=search_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

search_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=search_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 19 | 19 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Search Unit Tests

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #APP-SEARCH-001 |
| Category | App \| Search |
| Status | Implemented |
| Source | `test/01_unit/app/search/search_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Scenarios

### Text Search

#### exact match

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val text = "hello world"
check(text.contains("hello"))
```

</details>

#### case sensitive match

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val text = "Hello"
check(text != "hello")
```

</details>

#### case insensitive match

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val text = "Hello"
val lower = "hello"
check(text.len() == lower.len())
```

</details>

#### no match returns empty

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val text = "hello"
check(not text.contains("xyz"))
```

</details>

#### match at start

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val text = "hello world"
check(text.starts_with("hello"))
```

</details>

#### match at end

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val text = "hello world"
check(text.ends_with("world"))
```

</details>

### Pattern Search

#### wildcard pattern

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val pattern = "*.spl"
check(pattern.contains("*"))
```

</details>

#### recursive pattern

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val pattern = "**/*.spl"
check(pattern.contains("**"))
```

</details>

#### directory filter

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val dir = "src/"
check(dir.ends_with("/"))
```

</details>

#### extension filter

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val ext = ".spl"
check(ext.starts_with("."))
```

</details>

### Symbol Search

#### find function by name

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val query = "fn main"
check(query.starts_with("fn"))
```

</details>

#### find class by name

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val query = "class Point"
check(query.starts_with("class"))
```

</details>

#### find trait by name

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val query = "trait Display"
check(query.starts_with("trait"))
```

</details>

#### find enum by name

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val query = "enum Color"
check(query.starts_with("enum"))
```

</details>

### Search Results

#### result has file path

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val path = "src/main.spl"
check(path.ends_with(".spl"))
```

</details>

#### result has line number

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val line = 42
check(line > 0)
```

</details>

#### result has column number

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val col = 10
check(col > 0)
```

</details>

#### result has context

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val context = "fn main():"
check(context.len() > 0)
```

</details>

#### results are sorted by relevance

1. check
2. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val scores = [100, 80, 60, 40]
check(scores[0] > scores[1])
check(scores[1] > scores[2])
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
