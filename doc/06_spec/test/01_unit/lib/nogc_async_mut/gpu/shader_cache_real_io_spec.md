# Shader Cache Real Io Specification

> <details>

<!-- sdn-diagram:id=shader_cache_real_io_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=shader_cache_real_io_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

shader_cache_real_io_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=shader_cache_real_io_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 9 | 9 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Shader Cache Real Io Specification

## Scenarios

### Shader cache real I/O

#### shader_cache_is_persistent returns true

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(shader_cache_is_persistent()).to_equal(true)
```

</details>

#### store and lookup works in memory

1. shader cache store
   - Expected: result.found is true
   - Expected: result.size equals `2048`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
shader_cache_store("rio_abc", 2048)
val result = shader_cache_lookup("rio_abc")
expect(result.found).to_equal(true)
expect(result.size).to_equal(2048)
```

</details>

#### store writes file to disk

1. shader cache set directory
2. shader cache store
   - Expected: exists is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
shader_cache_set_directory("/tmp/simple_shader_cache_test")
shader_cache_store("rio_disk01", 512)
val exists = rt_file_exists("/tmp/simple_shader_cache_test/rio_disk01.spv")
expect(exists).to_equal(true)
```

</details>

#### lookup after invalidate falls back to disk

1. shader cache set directory
2. shader cache store
3. shader cache invalidate
   - Expected: result.found is true
   - Expected: result.size equals `1024`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
shader_cache_set_directory("/tmp/simple_shader_cache_test")
shader_cache_store("rio_fallback", 1024)
shader_cache_invalidate("rio_fallback")
val result = shader_cache_lookup("rio_fallback")
expect(result.found).to_equal(true)
expect(result.size).to_equal(1024)
```

</details>

#### set_directory changes cache path

1. shader cache set directory
2. shader cache store
   - Expected: exists is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
shader_cache_set_directory("/tmp/simple_shader_cache_alt")
shader_cache_store("rio_alt01", 256)
val exists = rt_file_exists("/tmp/simple_shader_cache_alt/rio_alt01.spv")
expect(exists).to_equal(true)
```

</details>

#### flush writes all entries to disk

1. shader cache set directory
2. shader cache store
3. shader cache store
4. shader cache flush
   - Expected: e1 is true
   - Expected: e2 is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
shader_cache_set_directory("/tmp/simple_shader_cache_flush")
shader_cache_store("rio_flush01", 100)
shader_cache_store("rio_flush02", 200)
shader_cache_flush()
val e1 = rt_file_exists("/tmp/simple_shader_cache_flush/rio_flush01.spv")
val e2 = rt_file_exists("/tmp/simple_shader_cache_flush/rio_flush02.spv")
expect(e1).to_equal(true)
expect(e2).to_equal(true)
```

</details>

#### hit and miss counts still work

1. shader cache store
2. shader cache lookup
3. shader cache lookup


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val hits_before = shader_cache_hit_count()
val misses_before = shader_cache_miss_count()
shader_cache_store("rio_hitcount", 64)
shader_cache_lookup("rio_hitcount")
shader_cache_lookup("rio_nosuch999")
expect(shader_cache_hit_count()).to_be_greater_than(hits_before)
expect(shader_cache_miss_count()).to_be_greater_than(misses_before)
```

</details>

#### empty hash rejected

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

#### zero size rejected

1. shader cache store
   - Expected: shader_cache_size() equals `before`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val before = shader_cache_size()
shader_cache_store("rio_zero", 0)
expect(shader_cache_size()).to_equal(before)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/nogc_async_mut/gpu/shader_cache_real_io_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- Shader cache real I/O

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 9 |
| Active scenarios | 9 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
