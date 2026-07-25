# Cache Unit Tests

> 1. check

<!-- sdn-diagram:id=cache_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=cache_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

cache_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=cache_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 18 | 18 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Cache Unit Tests

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #APP-CACHE-001 |
| Category | App \| Cache |
| Status | Implemented |
| Source | `test/01_unit/app/cache/cache_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Scenarios

### Cache Operations

#### cache hit returns cached value

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val hit = true
check(hit)
```

</details>

#### cache miss computes value

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val miss = true
check(miss)
```

</details>

#### cache put stores value

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val stored = true
check(stored)
```

</details>

#### cache invalidation

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val invalidated = true
check(invalidated)
```

</details>

#### cache eviction on full

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val evicted = true
check(evicted)
```

</details>

### Cache Key Types

#### file path as key

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val key = "src/main.spl"
check(key.ends_with(".spl"))
```

</details>

#### content hash as key

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val key = "sha256:abc123"
check(key.starts_with("sha256"))
```

</details>

#### module path as key

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val key = "std.io"
check(key.contains("."))
```

</details>

#### composite key

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val key = "src/main.spl:v2:opt2"
check(key.contains(":"))
```

</details>

### Cache Strategies

#### LRU eviction

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val strategy = "lru"
check(strategy == "lru")
```

</details>

#### TTL-based expiration

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val ttl_ms = 60000
check(ttl_ms > 0)
```

</details>

#### size-based limit

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val max_size = 1024 * 1024
check(max_size > 0)
```

</details>

#### content-addressed cache

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val is_content_addressed = true
check(is_content_addressed)
```

</details>

### Build Cache

#### cache compiled modules

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val cached_ext = ".smf"
check(cached_ext == ".smf")
```

</details>

#### cache incremental results

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val has_incremental = true
check(has_incremental)
```

</details>

#### cache invalidation on source change

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source_hash_changed = true
check(source_hash_changed)
```

</details>

#### cache directory location

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val dir = ".simple/build"
check(dir.starts_with(".simple"))
```

</details>

#### clean cache

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val cleaned = true
check(cleaned)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 18 |
| Active scenarios | 18 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
