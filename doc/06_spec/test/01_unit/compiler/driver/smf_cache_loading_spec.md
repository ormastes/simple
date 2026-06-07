# smf_cache_loading_spec

> SMF Cache Loading Specification

<!-- sdn-diagram:id=smf_cache_loading_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=smf_cache_loading_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

smf_cache_loading_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=smf_cache_loading_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 9 | 9 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# smf_cache_loading_spec

SMF Cache Loading Specification

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #INTERP-SMF-001 to #INTERP-SMF-005 |
| Category | Driver |
| Status | Active |
| Source | `test/01_unit/compiler/driver/smf_cache_loading_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

SMF Cache Loading Specification

Tests the interpreter's SMF cache lookup and fallback behavior.

## Scenarios

### SMF cache lookup

#### finds cached entry by source path

1. var cache = mock cache new
2. cache = mock cache add
   - Expected: entry.? is true
   - Expected: entry.unwrap().smf_path equals `build/smf/src_main.smf`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var cache = mock_cache_new()
cache = mock_cache_add(cache, "src/main.spl", "build/smf/src_main.smf", 42)
val entry = mock_cache_find(cache, "src/main.spl")
expect(entry.?).to_equal(true)
expect(entry.unwrap().smf_path).to_equal("build/smf/src_main.smf")
```

</details>

#### returns nil for missing source path

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val cache = mock_cache_new()
val entry = mock_cache_find(cache, "src/missing.spl")
expect(entry.?).to_equal(false)
```

</details>

#### finds correct entry among multiple

1. var cache = mock cache new
2. cache = mock cache add
3. cache = mock cache add
4. cache = mock cache add
   - Expected: entry.? is true
   - Expected: entry.unwrap().source_hash equals `20`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var cache = mock_cache_new()
cache = mock_cache_add(cache, "src/a.spl", "build/smf/a.smf", 10)
cache = mock_cache_add(cache, "src/b.spl", "build/smf/b.smf", 20)
cache = mock_cache_add(cache, "src/c.spl", "build/smf/c.smf", 30)
val entry = mock_cache_find(cache, "src/b.spl")
expect(entry.?).to_equal(true)
expect(entry.unwrap().source_hash).to_equal(20)
```

</details>

### SMF freshness check for interpreter

#### returns FRESH when hashes match

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = mock_validate(42, 42)
expect(result).to_equal(MOCK_FRESH)
```

</details>

#### returns STALE when hashes differ

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = mock_validate(42, 99)
expect(result).to_equal(MOCK_STALE)
```

</details>

#### returns MISSING when cached hash is zero

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = mock_validate(42, 0)
expect(result).to_equal(MOCK_MISSING)
```

</details>

### SMF cache fallback logic

#### loads from cache when fresh

1. var cache = mock cache new
2. cache = mock cache add
   - Expected: use_smf is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var cache = mock_cache_new()
cache = mock_cache_add(cache, "src/main.spl", "build/smf/main.smf", 100)
val entry = mock_cache_find(cache, "src/main.spl")
val status = mock_validate(100, entry.unwrap().source_hash)
# When FRESH, we load from SMF (not fallback)
val use_smf = status == MOCK_FRESH
expect(use_smf).to_equal(true)
```

</details>

#### falls back to interpreter when stale

1. var cache = mock cache new
2. cache = mock cache add
   - Expected: use_smf is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var cache = mock_cache_new()
cache = mock_cache_add(cache, "src/main.spl", "build/smf/main.smf", 100)
val entry = mock_cache_find(cache, "src/main.spl")
# Source changed (hash 200 != cached 100)
val status = mock_validate(200, entry.unwrap().source_hash)
val use_smf = status == MOCK_FRESH
expect(use_smf).to_equal(false)
```

</details>

#### falls back to interpreter when not in cache

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val cache = mock_cache_new()
val entry = mock_cache_find(cache, "src/main.spl")
val use_smf = entry.?
expect(use_smf).to_equal(false)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 9 |
| Active scenarios | 9 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
