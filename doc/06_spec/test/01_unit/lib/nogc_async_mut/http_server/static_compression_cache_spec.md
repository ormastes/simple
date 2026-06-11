# Static Compression Cache Specification

> <details>

<!-- sdn-diagram:id=static_compression_cache_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=static_compression_cache_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

static_compression_cache_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=static_compression_cache_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 8 | 8 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Static Compression Cache Specification

## Scenarios

### StaticCompressionCache

#### empty cache returns nil from get

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val cache = StaticCompressionCache.new(128, 16777216)
val result = cache.get("/index.html", "gzip")
expect(result == nil).to_equal(true)
```

</details>

#### put then get returns the cached bytes

1. cache put
   - Expected: result != nil is true
   - Expected: got.len() equals `payload.len()`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val cache = StaticCompressionCache.new(128, 16777216)
val payload = _make_bytes_10()
cache.put("/index.html", "gzip", payload)
val result = cache.get("/index.html", "gzip")
expect(result != nil).to_equal(true)
val got = result ?? []
expect(got.len()).to_equal(payload.len())
```

</details>

#### different encoding for same path is a cache miss until put

1. cache put
   - Expected: miss == nil is true
2. cache put
   - Expected: hit != nil is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val cache = StaticCompressionCache.new(128, 16777216)
val payload = _make_bytes_10()
cache.put("/style.css", "gzip", payload)
# "zstd" encoding not yet stored — must miss.
val miss = cache.get("/style.css", "zstd")
expect(miss == nil).to_equal(true)
# After putting the zstd variant, it hits.
val payload2 = _make_bytes_20()
cache.put("/style.css", "zstd", payload2)
val hit = cache.get("/style.css", "zstd")
expect(hit != nil).to_equal(true)
```

</details>

#### clear() empties the cache

1. cache put
2. cache put
3. cache clear
   - Expected: cache.entries.len() equals `0`
   - Expected: cache.current_size equals `0`
   - Expected: miss_a == nil is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val cache = StaticCompressionCache.new(128, 16777216)
cache.put("/a.html", "gzip", _make_bytes_10())
cache.put("/b.css", "lz4", _make_bytes_20())
cache.clear()
expect(cache.entries.len()).to_equal(0)
expect(cache.current_size).to_equal(0)
val miss_a = cache.get("/a.html", "gzip")
expect(miss_a == nil).to_equal(true)
```

</details>

#### LRU eviction: filling beyond count capacity evicts the least-recently-used

1. cache put
2. cache put
   - Expected: cache.get("/a.html", "gzip") != nil is true
   - Expected: cache.get("/b.css", "gzip") != nil is true
3. cache put
   - Expected: a_hit != nil is true
   - Expected: b_hit == nil is true
   - Expected: c_hit != nil is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Capacity of 2 entries. Put A then B. Put C forces eviction of A (LRU).
val cache = StaticCompressionCache.new(2, 16777216)
cache.put("/a.html", "gzip", _make_bytes_10())
cache.put("/b.css", "gzip", _make_bytes_20())
# Both present.
expect(cache.get("/a.html", "gzip") != nil).to_equal(true)
expect(cache.get("/b.css", "gzip") != nil).to_equal(true)
# After get("/a.html") above, A is MRU, B is LRU.
# Putting C should evict B.
cache.put("/c.js", "gzip", _make_bytes_30())
val a_hit = cache.get("/a.html", "gzip")
val b_hit = cache.get("/b.css", "gzip")
val c_hit = cache.get("/c.js", "gzip")
expect(a_hit != nil).to_equal(true)
expect(b_hit == nil).to_equal(true)
expect(c_hit != nil).to_equal(true)
```

</details>

#### get() promotes entry to MRU so subsequent eviction skips it

1. cache put
2. cache put
3. cache put
   - Expected: cache.get("/a.html", "gzip") != nil is true
   - Expected: cache.get("/b.css", "gzip") == nil is true
   - Expected: cache.get("/c.js", "gzip") != nil is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Put A then B. get(A) promotes A to MRU, making B the LRU.
# Putting C (capacity=2) evicts B, not A.
val cache = StaticCompressionCache.new(2, 16777216)
cache.put("/a.html", "gzip", _make_bytes_10())
cache.put("/b.css", "gzip", _make_bytes_20())
# Access A — promotes A to MRU; B becomes LRU.
val _ = cache.get("/a.html", "gzip")
# Adding C forces eviction of LRU = B.
cache.put("/c.js", "gzip", _make_bytes_30())
expect(cache.get("/a.html", "gzip") != nil).to_equal(true)
expect(cache.get("/b.css", "gzip") == nil).to_equal(true)
expect(cache.get("/c.js", "gzip") != nil).to_equal(true)
```

</details>

#### total-bytes bound triggers eviction when new entry would exceed max_bytes

1. cache put
2. cache put
   - Expected: cache.get("/a.html", "gzip") != nil is true
   - Expected: cache.get("/b.css", "gzip") != nil is true
3. cache put
   - Expected: cache.get("/a.html", "gzip") == nil is true
   - Expected: cache.get("/b.css", "gzip") != nil is true
   - Expected: cache.get("/c.js", "gzip") != nil is true
   - Expected: cache.current_size <= 25 is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# max_bytes = 25, each payload is 10 bytes.
# After 2 entries (20 bytes), adding a third (10 bytes → 30 total) evicts
# the oldest to make room.
val cache = StaticCompressionCache.new(128, 25)
cache.put("/a.html", "gzip", _make_bytes_10())
cache.put("/b.css", "gzip", _make_bytes_10())
# Both present (20 bytes total, within limit).
expect(cache.get("/a.html", "gzip") != nil).to_equal(true)
expect(cache.get("/b.css", "gzip") != nil).to_equal(true)
# After gets above, /b.css is MRU, /a.html is LRU.
# Adding /c.js (10 bytes) would push to 30 > 25 — must evict /a.html first.
cache.put("/c.js", "gzip", _make_bytes_10())
expect(cache.get("/a.html", "gzip") == nil).to_equal(true)
expect(cache.get("/b.css", "gzip") != nil).to_equal(true)
expect(cache.get("/c.js", "gzip") != nil).to_equal(true)
expect(cache.current_size <= 25).to_equal(true)
```

</details>

#### entry larger than max_bytes is silently rejected and cache is unchanged

1. cache put
2. cache put
   - Expected: cache.entries.len() equals `before_count`
   - Expected: cache.current_size equals `before_size`
   - Expected: cache.get("/a.html", "gzip") != nil is true
   - Expected: cache.get("/big.html", "gzip") == nil is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# max_bytes = 50. Put one valid 10-byte entry.
# Then try to put a 100-byte entry — must be rejected.
val cache = StaticCompressionCache.new(128, 50)
cache.put("/a.html", "gzip", _make_bytes_10())
val before_count = cache.entries.len()
val before_size = cache.current_size
# 100-byte payload exceeds max_bytes=50 → must be rejected.
cache.put("/big.html", "gzip", _make_bytes_100())
expect(cache.entries.len()).to_equal(before_count)
expect(cache.current_size).to_equal(before_size)
# The previously-stored entry is still present.
expect(cache.get("/a.html", "gzip") != nil).to_equal(true)
# The oversized entry was not stored.
expect(cache.get("/big.html", "gzip") == nil).to_equal(true)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/nogc_async_mut/http_server/static_compression_cache_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- StaticCompressionCache

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 8 |
| Active scenarios | 8 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
