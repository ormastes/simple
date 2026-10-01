# Static Compression Cache Specification

> Tests covering StaticCompressionCache.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 8 | 8 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Static Compression Cache Specification

## Scenarios

### StaticCompressionCache

#### empty cache returns nil from get

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- empty cache returns nil from get
   - Expected: result equals `nil`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("empty cache returns nil from get")
val cache = StaticCompressionCache.new(128, 16777216)
val result = cache.get("/index.html", "gzip")
expect(result).to_equal(nil)
```

</details>

#### put then get returns the cached bytes

- put then get returns the cached bytes
   - Expected: result != nil is true
   - Expected: got.len() equals `payload.len()`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("put then get returns the cached bytes")
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

- different encoding for same path is a cache miss until put
   - Expected: miss equals `nil`
   - Expected: hit != nil is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("different encoding for same path is a cache miss until put")
val cache = StaticCompressionCache.new(128, 16777216)
val payload = _make_bytes_10()
cache.put("/style.css", "gzip", payload)
# "zstd" encoding not yet stored — must miss.
val miss = cache.get("/style.css", "zstd")
expect(miss).to_equal(nil)
# After putting the zstd variant, it hits.
val payload2 = _make_bytes_20()
cache.put("/style.css", "zstd", payload2)
val hit = cache.get("/style.css", "zstd")
expect(hit != nil).to_equal(true)
```

</details>

#### clear() empties the cache

- clear() empties the cache
   - Expected: cache.entries.len() equals `0`
   - Expected: cache.current_size equals `0`
   - Expected: miss_a equals `nil`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("clear() empties the cache")
val cache = StaticCompressionCache.new(128, 16777216)
cache.put("/a.html", "gzip", _make_bytes_10())
cache.put("/b.css", "lz4", _make_bytes_20())
cache.clear()
expect(cache.entries.len()).to_equal(0)
expect(cache.current_size).to_equal(0)
val miss_a = cache.get("/a.html", "gzip")
expect(miss_a).to_equal(nil)
```

</details>

#### LRU eviction: filling beyond count capacity evicts the least-recently-used

- LRU eviction: filling beyond count capacity evicts the least-recently-used
   - Expected: cache.get("/a.html", "gzip") != nil is true
   - Expected: cache.get("/b.css", "gzip") != nil is true
   - Expected: a_hit != nil is true
   - Expected: b_hit equals `nil`
   - Expected: c_hit != nil is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 18 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("LRU eviction: filling beyond count capacity evicts the least-recently-used")
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
expect(b_hit).to_equal(nil)
expect(c_hit != nil).to_equal(true)
```

</details>

#### get() promotes entry to MRU so subsequent eviction skips it

- get() promotes entry to MRU so subsequent eviction skips it
   - Expected: cache.get("/a.html", "gzip") != nil is true
   - Expected: cache.get("/b.css", "gzip") equals `nil`
   - Expected: cache.get("/c.js", "gzip") != nil is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("get() promotes entry to MRU so subsequent eviction skips it")
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
expect(cache.get("/b.css", "gzip")).to_equal(nil)
expect(cache.get("/c.js", "gzip") != nil).to_equal(true)
```

</details>

#### total-bytes bound triggers eviction when new entry would exceed max_bytes

- total-bytes bound triggers eviction when new entry would exceed max_bytes
   - Expected: cache.get("/a.html", "gzip") != nil is true
   - Expected: cache.get("/b.css", "gzip") != nil is true
   - Expected: cache.get("/a.html", "gzip") equals `nil`
   - Expected: cache.get("/b.css", "gzip") != nil is true
   - Expected: cache.get("/c.js", "gzip") != nil is true
   - Expected: cache.current_size <= 25 is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 18 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("total-bytes bound triggers eviction when new entry would exceed max_bytes")
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
expect(cache.get("/a.html", "gzip")).to_equal(nil)
expect(cache.get("/b.css", "gzip") != nil).to_equal(true)
expect(cache.get("/c.js", "gzip") != nil).to_equal(true)
expect(cache.current_size <= 25).to_equal(true)
```

</details>

#### entry larger than max_bytes is silently rejected and cache is unchanged

- entry larger than max_bytes is silently rejected and cache is unchanged
   - Expected: cache.entries.len() equals `before_count`
   - Expected: cache.current_size equals `before_size`
   - Expected: cache.get("/a.html", "gzip") != nil is true
   - Expected: cache.get("/big.html", "gzip") equals `nil`


<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("entry larger than max_bytes is silently rejected and cache is unchanged")
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
expect(cache.get("/big.html", "gzip")).to_equal(nil)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/unit/lib/nogc_async_mut/http_server/static_compression_cache_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering StaticCompressionCache.
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

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-UNIT`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `26e5c84088c327bead08671ad66f56696dea4721ab3b8d46fbe42164cf5688b5`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `26e5c84088c327bead08671ad66f56696dea4721ab3b8d46fbe42164cf5688b5`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `26e5c84088c327bead08671ad66f56696dea4721ab3b8d46fbe42164cf5688b5`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **88/100**; effective score: **88/100**; blockers: **0**.

SSpec documentization score: 88/100
source: test/unit/lib/nogc_async_mut/http_server/static_compression_cache_spec.spl
mirror: doc/06_spec/unit/lib/nogc_async_mut/http_server/static_compression_cache_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=80
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/unit/lib/nogc_async_mut/http_server/static_compression_cache_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/unit/lib/nogc_async_mut/http_server/static_compression_cache_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/unit/lib/nogc_async_mut/http_server/static_compression_cache_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-20): 2 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/unit/lib/nogc_async_mut/http_server/static_compression_cache_spec.spl:63:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'empty cache returns nil from get' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/lib/nogc_async_mut/http_server/static_compression_cache_spec.spl:70:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'put then get returns the cached bytes' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/lib/nogc_async_mut/http_server/static_compression_cache_spec.spl:81:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'different encoding for same path is a cache miss until put' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
