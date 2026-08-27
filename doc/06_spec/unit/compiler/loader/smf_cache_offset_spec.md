# Smf Cache Offset Specification

> Tests covering Smf Cache Offset.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 3 | 3 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Smf Cache Offset Specification

## Scenarios

### Smf Cache Offset

#### stores cache statistics values

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- stores cache statistics values
   - Expected: stats.total_files equals `5`
   - Expected: stats.total_memory equals `1024`
   - Expected: stats.cache_hits equals `10`
   - Expected: stats.cache_misses equals `3`


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("stores cache statistics values")
val stats = CacheStats(
    total_files: 5,
    total_memory: 1024,
    cache_hits: 10,
    cache_misses: 3
)

expect(stats.total_files).to_equal(5)
expect(stats.total_memory).to_equal(1024)
expect(stats.cache_hits).to_equal(10)
expect(stats.cache_misses).to_equal(3)
```

</details>

#### creates an empty cache by default

- creates an empty cache by default
   - Expected: cache.cached_count() equals `0`
   - Expected: cache.is_cached("missing.smf") is false
   - Expected: cache.get_stats().total_files equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("creates an empty cache by default")
val cache = SmfCache.new()
expect(cache.cached_count()).to_equal(0)
expect(cache.is_cached("missing.smf")).to_equal(false)
expect(cache.get_stats().total_files).to_equal(0)
```

</details>

#### decodes little-endian u32 values

- decodes little-endian u32 values
   - Expected: bytes_to_u32([1, 0, 0, 0]) equals `1`
   - Expected: bytes_to_u32([0, 1, 0, 0]) equals `256`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("decodes little-endian u32 values")
expect(bytes_to_u32([1, 0, 0, 0])).to_equal(1)
expect(bytes_to_u32([0, 1, 0, 0])).to_equal(256)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/unit/compiler/loader/smf_cache_offset_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering Smf Cache Offset.
- Smf Cache Offset

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 3 |
| Active scenarios | 3 |
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

- Canonical SPipe generation for source `93726188fc450920c448636c2ed8fab23475e8b5a695223d0376be5e87a197d2`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `93726188fc450920c448636c2ed8fab23475e8b5a695223d0376be5e87a197d2`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `93726188fc450920c448636c2ed8fab23475e8b5a695223d0376be5e87a197d2`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **86/100**; effective score: **86/100**; blockers: **0**.

SSpec documentization score: 86/100
source: test/unit/compiler/loader/smf_cache_offset_spec.spl
mirror: doc/06_spec/unit/compiler/loader/smf_cache_offset_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/unit/compiler/loader/smf_cache_offset_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/unit/compiler/loader/smf_cache_offset_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/unit/compiler/loader/smf_cache_offset_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 8 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/unit/compiler/loader/smf_cache_offset_spec.spl:11:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'stores cache statistics values' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/compiler/loader/smf_cache_offset_spec.spl:26:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'creates an empty cache by default' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/compiler/loader/smf_cache_offset_spec.spl:34:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'decodes little-endian u32 values' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
