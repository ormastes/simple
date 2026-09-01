# Glyph Cache Index Plain Specification

> Tests covering GlyphCache plain glyph-index lookup.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 2 | 2 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Glyph Cache Index Plain Specification

## Scenarios

### GlyphCache plain glyph-index lookup

#### returns the cached shaped glyph without an optional aggregate

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- returns the cached shaped glyph without an optional aggregate
   - Expected: found.glyph_index equals `3`
   - Expected: found.pixels.len() equals `1`
   - Expected: cache.stats().hits equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("returns the cached shaped glyph without an optional aggregate")
var cache = GlyphCache.new(8)
cache.insert(CachedGlyph(
    codepoint: -1, face_id: 11, face_generation: 7, glyph_index: 3,
    font_size: 16, width: 1, height: 1, advance: 1,
    bearing_x: 0, bearing_y: 0, pixels: [255u8]))
val found = cache.lookup_index(11, 7, 3, 16)
expect(found.glyph_index).to_equal(3)
expect(found.pixels.len()).to_equal(1)
expect(cache.stats().hits).to_equal(1)
```

</details>

#### returns an explicit empty sentinel for every shaped-key miss

- returns an explicit empty sentinel for every shaped-key miss
   - Expected: generation_miss.glyph_index equals `-1`
   - Expected: face_miss.glyph_index equals `-1`
   - Expected: glyph_miss.glyph_index equals `-1`
   - Expected: size_miss.glyph_index equals `-1`
   - Expected: cache.stats().misses equals `4`


<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("returns an explicit empty sentinel for every shaped-key miss")
var cache = GlyphCache.new(8)
cache.insert(CachedGlyph(
    codepoint: -1, face_id: 11, face_generation: 7, glyph_index: 3,
    font_size: 16, width: 1, height: 1, advance: 1,
    bearing_x: 0, bearing_y: 0, pixels: [255u8]))
val generation_miss = cache.lookup_index(11, 8, 3, 16)
val face_miss = cache.lookup_index(12, 7, 3, 16)
val glyph_miss = cache.lookup_index(11, 7, 4, 16)
val size_miss = cache.lookup_index(11, 7, 3, 17)
expect(generation_miss.glyph_index).to_equal(-1)
expect(face_miss.glyph_index).to_equal(-1)
expect(glyph_miss.glyph_index).to_equal(-1)
expect(size_miss.glyph_index).to_equal(-1)
expect(cache.stats().misses).to_equal(4)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/common/text_layout/glyph_cache_index_plain_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering GlyphCache plain glyph-index lookup.
- GlyphCache plain glyph-index lookup

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 2 |
| Active scenarios | 2 |
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

- Canonical SPipe generation for source `3aa8aeec5f239857a3a5c46fecaa0df4a3324d1d29476ffc7653048c0643d8ca`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `3aa8aeec5f239857a3a5c46fecaa0df4a3324d1d29476ffc7653048c0643d8ca`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `3aa8aeec5f239857a3a5c46fecaa0df4a3324d1d29476ffc7653048c0643d8ca`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **88/100**; effective score: **88/100**; blockers: **0**.

SSpec documentization score: 88/100
source: test/01_unit/lib/common/text_layout/glyph_cache_index_plain_spec.spl
mirror: doc/06_spec/01_unit/lib/common/text_layout/glyph_cache_index_plain_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=80 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/lib/common/text_layout/glyph_cache_index_plain_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/lib/common/text_layout/glyph_cache_index_plain_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/lib/common/text_layout/glyph_cache_index_plain_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 8 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/lib/common/text_layout/glyph_cache_index_plain_spec.spl:16:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'returns the cached shaped glyph without an optional aggregate' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/common/text_layout/glyph_cache_index_plain_spec.spl:29:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'returns an explicit empty sentinel for every shaped-key miss' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
