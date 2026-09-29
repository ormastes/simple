# Helpers Text Cache Specification

> Tests covering Engine2D text blit cache.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 1 | 1 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Helpers Text Cache Specification

## Scenarios

### Engine2D text blit cache

#### keeps repeated Draw IR labels on the hot cache path without rescanning entries

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- keeps repeated Draw IR labels on the hot cache path without rescanning entries
   - Expected: first.is_empty() is false
   - Expected: second.width equals `first.width`
   - Expected: second.height equals `first.height`
   - Expected: cache.cache_misses equals `1`
   - Expected: cache.cache_hits equals `1`
   - Expected: cache.lookup_scan_count equals `scans_after_miss`
   - Expected: third.is_empty() is false
   - Expected: cache.lookup_scan_count > scans_after_miss is true
   - Expected: fourth.width equals `first.width`
   - Expected: cache.bucket_hits equals `1`
   - Expected: cache.cache_hits equals `2`
   - Expected: cache.lookup_scan_count equals `scans_after_other`


<details>
<summary>Executable SSpec</summary>

Runnable source: 23 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("keeps repeated Draw IR labels on the hot cache path without rescanning entries")
var cache = TextBlitCache.new()
val first = cache.transparent_blit_buffer("Repeat", 0xff111111u32, 14)
val scans_after_miss = cache.lookup_scan_count
val second = cache.transparent_blit_buffer("Repeat", 0xff111111u32, 14)

expect(first.is_empty()).to_equal(false)
expect(second.width).to_equal(first.width)
expect(second.height).to_equal(first.height)
expect(cache.cache_misses).to_equal(1)
expect(cache.cache_hits).to_equal(1)
expect(cache.lookup_scan_count).to_equal(scans_after_miss)

val third = cache.transparent_blit_buffer("Other", 0xff111111u32, 14)
expect(third.is_empty()).to_equal(false)
expect(cache.lookup_scan_count > scans_after_miss).to_equal(true)
val scans_after_other = cache.lookup_scan_count
val fourth = cache.transparent_blit_buffer("Repeat", 0xff111111u32, 14)
expect(fourth.width).to_equal(first.width)
expect(cache.bucket_hits).to_equal(1)
expect(cache.cache_hits).to_equal(2)
expect(cache.lookup_scan_count).to_equal(scans_after_other)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/gpu/engine2d/helpers_text_cache_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering Engine2D text blit cache.
- Engine2D text blit cache

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 1 |
| Active scenarios | 1 |
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

- Canonical SPipe generation for source `aba8539fc9ec7c265fda50bf4b7aed251bc622d0ebb4e416a7f6bac0e2beb534`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `aba8539fc9ec7c265fda50bf4b7aed251bc622d0ebb4e416a7f6bac0e2beb534`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `aba8539fc9ec7c265fda50bf4b7aed251bc622d0ebb4e416a7f6bac0e2beb534`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **89/100**; effective score: **89/100**; blockers: **0**.

SSpec documentization score: 89/100
source: test/01_unit/lib/gpu/engine2d/helpers_text_cache_spec.spl
mirror: doc/06_spec/01_unit/lib/gpu/engine2d/helpers_text_cache_spec.md (current)
findings: 4 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=90 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/lib/gpu/engine2d/helpers_text_cache_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/lib/gpu/engine2d/helpers_text_cache_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/lib/gpu/engine2d/helpers_text_cache_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 4 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/lib/gpu/engine2d/helpers_text_cache_spec.spl:16:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'keeps repeated Draw IR labels on the hot cache path without rescanning entries' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
