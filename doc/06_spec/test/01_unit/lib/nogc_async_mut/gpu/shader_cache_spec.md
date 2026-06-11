# Shader Cache Specification

> <details>

<!-- sdn-diagram:id=shader_cache_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=shader_cache_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

shader_cache_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=shader_cache_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 9 | 9 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Shader Cache Specification

## Scenarios

### Shader cache

#### lookup on empty cache returns found=false

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = shader_cache_lookup("deadbeef")
expect(result.found).to_equal(false)
```

</details>

#### store and lookup returns found=true with correct size

1. shader cache store
   - Expected: result.found is true
   - Expected: result.size equals `4096`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
shader_cache_store("abc123", 4096)
val result = shader_cache_lookup("abc123")
expect(result.found).to_equal(true)
expect(result.size).to_equal(4096)
```

</details>

#### cache size increases after store

1. shader cache store


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val before = shader_cache_size()
shader_cache_store("newshader01", 2048)
val after = shader_cache_size()
expect(after).to_be_greater_than(before)
```

</details>

#### hit count increments on successful lookup

1. shader cache store
2. shader cache lookup


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
shader_cache_store("hitme", 1024)
val hits_before = shader_cache_hit_count()
shader_cache_lookup("hitme")
expect(shader_cache_hit_count()).to_be_greater_than(hits_before)
```

</details>

#### miss count increments on failed lookup

1. shader cache lookup


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val misses_before = shader_cache_miss_count()
shader_cache_lookup("nosuchshader99")
expect(shader_cache_miss_count()).to_be_greater_than(misses_before)
```

</details>

#### store with empty hash is ignored

1. shader cache store
   - Expected: shader_cache_size() equals `before`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val before = shader_cache_size()
shader_cache_store("", 1024)
expect(shader_cache_size()).to_equal(before)
```

</details>

#### store with zero size is ignored

1. shader cache store
   - Expected: shader_cache_size() equals `before`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val before = shader_cache_size()
shader_cache_store("zerosize", 0)
expect(shader_cache_size()).to_equal(before)
```

</details>

#### invalidate removes entry from cache

1. shader cache store
2. shader cache invalidate
   - Expected: result.found is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
shader_cache_store("toremove", 512)
shader_cache_invalidate("toremove")
val result = shader_cache_lookup("toremove")
expect(result.found).to_equal(false)
```

</details>

#### duplicate store does not create second entry

1. shader cache store
2. shader cache store
   - Expected: shader_cache_size() equals `before`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
shader_cache_store("dupkey", 100)
val before = shader_cache_size()
shader_cache_store("dupkey", 200)
expect(shader_cache_size()).to_equal(before)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/nogc_async_mut/gpu/shader_cache_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- Shader cache

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 9 |
| Active scenarios | 9 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
