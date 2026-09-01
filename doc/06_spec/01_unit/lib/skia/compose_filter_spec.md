# Skia Compose Filter Specification

> Tests for `compose_filter_new`, `compose_filter_new2`, and `apply_compose` — the multi-stage image-filter composer mirroring Skia's `SkImageFilters::Compose(outer, inner)`.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 5 | 5 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Skia Compose Filter Specification

Tests for `compose_filter_new`, `compose_filter_new2`, and `apply_compose` — the multi-stage image-filter composer mirroring Skia's `SkImageFilters::Compose(outer, inner)`.

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #SKI-COMPOSE |
| Category | Stdlib |
| Difficulty | 2/5 |
| Status | Implemented |
| Source | `test/01_unit/lib/skia/compose_filter_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests for `compose_filter_new`, `compose_filter_new2`, and `apply_compose` —
the multi-stage image-filter composer mirroring Skia's
`SkImageFilters::Compose(outer, inner)`.

## Scenarios

### compose_filter

#### compose_filter: single Identity stage returns input unchanged

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- compose_filter: single Identity stage returns input unchanged
   - Expected: out.width equals `src.width`
   - Expected: out.height equals `src.height`
   - Expected: _bitmap_diff(src, out) equals `0 as i64`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("compose_filter: single Identity stage returns input unchanged")
val src = _make_test_bitmap(8, 6)
var stages = [FilterNode]()
stages.push(filter_node_identity())
val compose = compose_filter_new(stages)
val out = apply_compose(src, compose)
expect(out.width).to_equal(src.width)
expect(out.height).to_equal(src.height)
expect(_bitmap_diff(src, out)).to_equal(0 as i64)
```

</details>

#### compose_filter: two Identity stages return input unchanged

- compose_filter: two Identity stages return input unchanged
   - Expected: out.width equals `src.width`
   - Expected: out.height equals `src.height`
   - Expected: _bitmap_diff(src, out) equals `0 as i64`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("compose_filter: two Identity stages return input unchanged")
val src = _make_test_bitmap(8, 6)
val compose = compose_filter_new2(filter_node_identity(), filter_node_identity())
val out = apply_compose(src, compose)
expect(out.width).to_equal(src.width)
expect(out.height).to_equal(src.height)
expect(_bitmap_diff(src, out)).to_equal(0 as i64)
```

</details>

#### compose_filter: Blur then Invert produces a visibly different output than either alone

- compose_filter: Blur then Invert produces a visibly different output than either alone


<details>
<summary>Executable SSpec</summary>

Runnable source: 21 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("compose_filter: Blur then Invert produces a visibly different output than either alone")
val src = _make_test_bitmap(12, 8)
val blur_node = filter_node_blur(blur_filter_new(2.0, 2.0))
val invert_node = filter_node_color(color_filter_invert())

var blur_only_stages = [FilterNode]()
blur_only_stages.push(blur_node)
val blur_only_out = apply_compose(src, compose_filter_new(blur_only_stages))

var invert_only_stages = [FilterNode]()
invert_only_stages.push(invert_node)
val invert_only_out = apply_compose(src, compose_filter_new(invert_only_stages))

val composed = apply_compose(src, compose_filter_new2(blur_node, invert_node))

# Composed result must differ from each single-stage result.
expect(_bitmap_diff(composed, blur_only_out)).to_be_greater_than(0 as i64)
expect(_bitmap_diff(composed, invert_only_out)).to_be_greater_than(0 as i64)
# And it should differ from the original src too.
expect(_bitmap_diff(composed, src)).to_be_greater_than(0 as i64)
```

</details>

#### compose_filter: empty stages list returns input unchanged (or handles gracefully)

- compose_filter: empty stages list returns input unchanged (or handles gracefully)
   - Expected: out.width equals `src.width`
   - Expected: out.height equals `src.height`
   - Expected: _bitmap_diff(src, out) equals `0 as i64`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("compose_filter: empty stages list returns input unchanged (or handles gracefully)")
val src = _make_test_bitmap(5, 5)
val empty_stages = [FilterNode]()
val compose = compose_filter_new(empty_stages)
val out = apply_compose(src, compose)
expect(out.width).to_equal(src.width)
expect(out.height).to_equal(src.height)
expect(_bitmap_diff(src, out)).to_equal(0 as i64)
```

</details>

#### compose_filter: order matters — apply_compose(src, [Blur, Invert]) differs from apply_compose(src, [Invert, Blur])

- compose_filter: order matters — apply_compose(src, [Blur, Invert]) differs from apply_compose(src, [Invert, Blur])


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("compose_filter: order matters — apply_compose(src, [Blur, Invert]) differs from apply_compose(src, [Invert, Blur])")
val src = _make_test_bitmap(12, 8)
val blur_node = filter_node_blur(blur_filter_new(2.5, 2.5))
val invert_node = filter_node_color(color_filter_invert())

val blur_then_invert = apply_compose(src, compose_filter_new2(blur_node, invert_node))
val invert_then_blur = apply_compose(src, compose_filter_new2(invert_node, blur_node))

# Blur and invert do not commute exactly because blur clamps then invert
# negates around 255; the orders must produce different bitmaps.
expect(_bitmap_diff(blur_then_invert, invert_then_blur)).to_be_greater_than(0 as i64)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 5 |
| Active scenarios | 5 |
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

- Canonical SPipe generation for source `fe5d9e7b01f5d1f2920f2df2bfcccdb36fc1a3a02c7908b8df92b783b407f06f`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `fe5d9e7b01f5d1f2920f2df2bfcccdb36fc1a3a02c7908b8df92b783b407f06f`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `fe5d9e7b01f5d1f2920f2df2bfcccdb36fc1a3a02c7908b8df92b783b407f06f`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/01_unit/lib/skia/compose_filter_spec.spl
mirror: doc/06_spec/01_unit/lib/skia/compose_filter_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/lib/skia/compose_filter_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/lib/skia/compose_filter_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/lib/skia/compose_filter_spec.spl:74:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'compose_filter: single Identity stage returns input unchanged' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/skia/compose_filter_spec.spl:86:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'compose_filter: two Identity stages return input unchanged' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/skia/compose_filter_spec.spl:96:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'compose_filter: Blur then Invert produces a visibly different output than either alone' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
