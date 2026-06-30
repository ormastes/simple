# Physics Contact Cache Specification

> 1. var cache = ContactCache create

<!-- sdn-diagram:id=physics_contact_cache_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=physics_contact_cache_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

physics_contact_cache_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=physics_contact_cache_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 4 | 4 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Physics Contact Cache Specification

## Scenarios

### Physics2 ContactCache

#### store and retrieve cached impulse

1. var cache = ContactCache create
2. store one
   - Expected: result.0 equals `5.0`
   - Expected: result.1 equals `1.5`
   - Expected: result.2 is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var cache = ContactCache.create()
store_one(cache, 0, 1, 0, 0, 5.0, 1.5)
val result = cache.find_cached(0, 1, 0, 0)
expect(result.0).to_equal(5.0)
expect(result.1).to_equal(1.5)
expect(result.2).to_equal(true)
```

</details>

#### miss returns zero

1. var cache = ContactCache create
   - Expected: result.0 equals `0.0`
   - Expected: result.1 equals `0.0`
   - Expected: result.2 is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var cache = ContactCache.create()
val result = cache.find_cached(99, 100, 0, 0)
expect(result.0).to_equal(0.0)
expect(result.1).to_equal(0.0)
expect(result.2).to_equal(false)
```

</details>

#### clear empties cache

1. var cache = ContactCache create
2. store one
3. cache clear
   - Expected: result.2 is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var cache = ContactCache.create()
store_one(cache, 0, 1, 0, 0, 3.0, 0.5)
cache.clear()
val result = cache.find_cached(0, 1, 0, 0)
expect(result.2).to_equal(false)
```

</details>

#### multiple contacts stored

1. var cache = ContactCache create
2. store three
   - Expected: r0.2 is true
   - Expected: r1.2 is true
   - Expected: r2.2 is true
   - Expected: r0.0 equals `1.0`
   - Expected: r1.0 equals `2.0`
   - Expected: r2.0 equals `3.0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var cache = ContactCache.create()
store_three(cache)
val r0 = cache.find_cached(0, 1, 0, 0)
val r1 = cache.find_cached(1, 2, 0, 0)
val r2 = cache.find_cached(2, 3, 0, 0)
expect(r0.2).to_equal(true)
expect(r1.2).to_equal(true)
expect(r2.2).to_equal(true)
expect(r0.0).to_equal(1.0)
expect(r1.0).to_equal(2.0)
expect(r2.0).to_equal(3.0)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/03_system/engine/physics_contact_cache_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- Physics2 ContactCache

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 4 |
| Active scenarios | 4 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
