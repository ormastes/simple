# Shader Cache Specification

> Tests covering Shader cache.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 9 | 9 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Shader Cache Specification

## Scenarios

### Shader cache

#### lookup on empty cache returns found=false

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- lookup on empty cache returns found=false
   - Expected: result.found is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("lookup on empty cache returns found=false")
val result = shader_cache_lookup("deadbeef")
expect(result.found).to_equal(false)
```

</details>

#### store and lookup returns found=true with correct size

- store and lookup returns found=true with correct size
   - Expected: result.found is true
   - Expected: result.size equals `4096`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("store and lookup returns found=true with correct size")
shader_cache_store("abc123", 4096)
val result = shader_cache_lookup("abc123")
expect(result.found).to_equal(true)
expect(result.size).to_equal(4096)
```

</details>

#### cache size increases after store

- cache size increases after store


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("cache size increases after store")
val before = shader_cache_size()
shader_cache_store("newshader01", 2048)
val after = shader_cache_size()
expect(after).to_be_greater_than(before)
```

</details>

#### hit count increments on successful lookup

- hit count increments on successful lookup


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("hit count increments on successful lookup")
shader_cache_store("hitme", 1024)
val hits_before = shader_cache_hit_count()
shader_cache_lookup("hitme")
expect(shader_cache_hit_count()).to_be_greater_than(hits_before)
```

</details>

#### miss count increments on failed lookup

- miss count increments on failed lookup


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("miss count increments on failed lookup")
val misses_before = shader_cache_miss_count()
shader_cache_lookup("nosuchshader99")
expect(shader_cache_miss_count()).to_be_greater_than(misses_before)
```

</details>

#### store with empty hash is ignored

- store with empty hash is ignored
   - Expected: shader_cache_size() equals `before`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("store with empty hash is ignored")
val before = shader_cache_size()
shader_cache_store("", 1024)
expect(shader_cache_size()).to_equal(before)
```

</details>

#### store with zero size is ignored

- store with zero size is ignored
   - Expected: shader_cache_size() equals `before`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("store with zero size is ignored")
val before = shader_cache_size()
shader_cache_store("zerosize", 0)
expect(shader_cache_size()).to_equal(before)
```

</details>

#### invalidate removes entry from cache

- invalidate removes entry from cache
   - Expected: result.found is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("invalidate removes entry from cache")
shader_cache_store("toremove", 512)
shader_cache_invalidate("toremove")
val result = shader_cache_lookup("toremove")
expect(result.found).to_equal(false)
```

</details>

#### duplicate store does not create second entry

- duplicate store does not create second entry
   - Expected: shader_cache_size() equals `before`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("duplicate store does not create second entry")
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
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering Shader cache.
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

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-LIB`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `9c82afedc6ee285505502b7585ab34c8c77d2a2313e53d57e54d711d028cc4b0`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `9c82afedc6ee285505502b7585ab34c8c77d2a2313e53d57e54d711d028cc4b0`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `9c82afedc6ee285505502b7585ab34c8c77d2a2313e53d57e54d711d028cc4b0`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **90/100**; effective score: **90/100**; blockers: **0**.

SSpec documentization score: 90/100
source: test/01_unit/lib/nogc_async_mut/gpu/shader_cache_spec.spl
mirror: doc/06_spec/01_unit/lib/nogc_async_mut/gpu/shader_cache_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=90
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/lib/nogc_async_mut/gpu/shader_cache_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/lib/nogc_async_mut/gpu/shader_cache_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/lib/nogc_async_mut/gpu/shader_cache_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-10): 1 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/lib/nogc_async_mut/gpu/shader_cache_spec.spl:25:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'lookup on empty cache returns found=false' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/nogc_async_mut/gpu/shader_cache_spec.spl:31:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'store and lookup returns found=true with correct size' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/nogc_async_mut/gpu/shader_cache_spec.spl:39:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'cache size increases after store' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
