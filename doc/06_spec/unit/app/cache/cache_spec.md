# Cache Specification

> Tests covering Cache Operations, Cache Key Types, Cache Strategies, Build Cache.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 18 | 18 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Cache Specification

## Scenarios

### Cache Operations

#### cache hit returns cached value

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- cache hit returns cached value


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("cache hit returns cached value")
val hit = true
check(hit)
```

</details>

#### cache miss computes value

- cache miss computes value


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("cache miss computes value")
val miss = true
check(miss)
```

</details>

#### cache put stores value

- cache put stores value


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("cache put stores value")
val stored = true
check(stored)
```

</details>

#### cache invalidation

- cache invalidation


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("cache invalidation")
val invalidated = true
check(invalidated)
```

</details>

#### cache eviction on full

- cache eviction on full


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("cache eviction on full")
val evicted = true
check(evicted)
```

</details>

### Cache Key Types

#### file path as key

- file path as key


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("file path as key")
val key = "src/main.spl"
check(key.ends_with(".spl"))
```

</details>

#### content hash as key

- content hash as key


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("content hash as key")
val key = "sha256:abc123"
check(key.starts_with("sha256"))
```

</details>

#### module path as key

- module path as key


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("module path as key")
val key = "std.io"
check(key.contains("."))
```

</details>

#### composite key

- composite key


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("composite key")
val key = "src/main.spl:v2:opt2"
check(key.contains(":"))
```

</details>

### Cache Strategies

#### LRU eviction

- LRU eviction


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("LRU eviction")
val strategy = "lru"
check(strategy == "lru")
```

</details>

#### TTL-based expiration

- TTL-based expiration


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("TTL-based expiration")
val ttl_ms = 60000
check(ttl_ms > 0)
```

</details>

#### size-based limit

- size-based limit


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("size-based limit")
val max_size = 1024 * 1024
check(max_size > 0)
```

</details>

#### content-addressed cache

- content-addressed cache


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("content-addressed cache")
val is_content_addressed = true
check(is_content_addressed)
```

</details>

### Build Cache

#### cache compiled modules

- cache compiled modules


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("cache compiled modules")
val cached_ext = ".smf"
check(cached_ext == ".smf")
```

</details>

#### cache incremental results

- cache incremental results


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("cache incremental results")
val has_incremental = true
check(has_incremental)
```

</details>

#### cache invalidation on source change

- cache invalidation on source change


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("cache invalidation on source change")
val source_hash_changed = true
check(source_hash_changed)
```

</details>

#### cache directory location

- cache directory location


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("cache directory location")
val dir = ".simple/build"
check(dir.starts_with(".simple"))
```

</details>

#### clean cache

- clean cache


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("clean cache")
val cleaned = true
check(cleaned)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/unit/app/cache/cache_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering Cache Operations, Cache Key Types, Cache Strategies, Build Cache.
- Cache Operations
- Cache Key Types
- Cache Strategies
- Build Cache

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 18 |
| Active scenarios | 18 |
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

- Canonical SPipe generation for source `43fed535fc04f6bd563f7dc8a8ede2b1b3ae7702be368f31e8850ee9fd0ff9ef`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `43fed535fc04f6bd563f7dc8a8ede2b1b3ae7702be368f31e8850ee9fd0ff9ef`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `43fed535fc04f6bd563f7dc8a8ede2b1b3ae7702be368f31e8850ee9fd0ff9ef`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/unit/app/cache/cache_spec.spl
mirror: doc/06_spec/unit/app/cache/cache_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/unit/app/cache/cache_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/unit/app/cache/cache_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/unit/app/cache/cache_spec.spl:18:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'cache hit returns cached value' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/app/cache/cache_spec.spl:24:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'cache miss computes value' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/app/cache/cache_spec.spl:30:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'cache put stores value' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
