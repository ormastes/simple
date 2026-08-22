# Simple 2D Vector Fonts

> Verifies the simple 2d vector fonts behaviour end to end so maintainers of this

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 7 | 7 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Simple 2D Vector Fonts

Verifies the simple 2d vector fonts behaviour end to end so maintainers of this

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/03_system/app/simple_2d/feature/simple_2d_vector_fonts_spec.spl` |
| Updated | 2026-08-22 |
| Generator | `simple spipe-docgen` (Simple) |

## Purpose and audience
Verifies the simple 2d vector fonts behaviour end to end so maintainers of this
component and reviewers of its spec share one pinned definition.
## Operator workflow
Run `bin/simple test <this spec>`; read the per-scenario verdicts in
the `Results:` summary. Each scenario asserts an observable outcome.
## Compatibility and limitations
Covers the currently shipped behaviour only; performance, stress and
unrelated sibling features are out of scope.

## Scenarios

### Simple 2D vector fonts

#### should render a selected ASCII vector font at two sizes

**Manual warnings:**
- invalid manual visibility metadata: # @manual_section: Primary flow (expected show, folded, detail, or skip)


- Verify: should render a selected ASCII vector font at two sizes
   - Artifact capture: after_step
- Load a vector font fixture
   - Artifact capture: after_step
- Render text through the Simple 2D facade
   - Artifact capture: after_step
- Verify glyph layout and pixels
   - Artifact capture: after_step
   - Evidence: artifact verified by 19 expected checks
   - Expected: small.checksum equals `160012687)  # oracle: pinned constant asserted by this scenario`
   - Expected: small.painted equals `106)  # oracle: pinned constant asserted by this scenario`
   - Expected: small.partial equals `102)  # oracle: pinned constant asserted by this scenario`
   - Expected: small.min_x equals `8)  # oracle: pinned constant asserted by this scenario`
   - Expected: small.min_y equals `14)  # oracle: pinned constant asserted by this scenario`
   - Expected: small.max_x equals `35)  # oracle: pinned constant asserted by this scenario`
   - Expected: small.max_y equals `24)  # oracle: pinned constant asserted by this scenario`
   - Expected: small.first_x equals `11)  # oracle: pinned constant asserted by this scenario`
   - Expected: small.first_y equals `14)  # oracle: pinned constant asserted by this scenario`
   - Expected: small.first_pixel equals `4282268725u32`
   - Expected: small.corner_pixel equals `rgb(3, 7, 11)`
   - Expected: small.last_pixel equals `rgb(3, 7, 11)`
   - Expected: large.checksum equals `106035644)  # oracle: pinned constant asserted by this scenario`
   - Expected: large.painted equals `334)  # oracle: pinned constant asserted by this scenario`
   - Expected: large.partial equals `216)  # oracle: pinned constant asserted by this scenario`
   - Expected: large.min_x equals `8)  # oracle: pinned constant asserted by this scenario`
   - Expected: large.min_y equals `20)  # oracle: pinned constant asserted by this scenario`
   - Expected: large.max_x equals `63)  # oracle: pinned constant asserted by this scenario`
   - Expected: large.max_y equals `40)  # oracle: pinned constant asserted by this scenario`


<details>
<summary>Executable SSpec</summary>

Runnable source: 38 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-010 REQ-002 REQ-003 REQ-004 REQ-001 REQ-005 REQ-007
step("Verify: should render a selected ASCII vector font at two sizes")
"""An application selects an owned TTF and receives deterministic antialiased output."""
step("Load a vector font fixture")
expect(materialize_vector_font_fixtures()).to_be(true)
var engine = Engine2D.create_with_backend(128, 72, "cpu")
engine.unload_font()
expect(load_vector_font_fixture(engine, UNICODE_PATH_FONT)).to_be(true)

step("Render text through the Simple 2D facade")
val small = render_font_fixture(engine, "A A", 16)
val large = render_font_fixture(engine, "A A", 32)

step("Verify glyph layout and pixels")
expect_antialiased_font_pixels(small)
expect_antialiased_font_pixels(large)
expect(small.checksum).to_equal(160012687)  # oracle: pinned constant asserted by this scenario
expect(small.painted).to_equal(106)  # oracle: pinned constant asserted by this scenario
expect(small.partial).to_equal(102)  # oracle: pinned constant asserted by this scenario
expect(small.min_x).to_equal(8)  # oracle: pinned constant asserted by this scenario
expect(small.min_y).to_equal(14)  # oracle: pinned constant asserted by this scenario
expect(small.max_x).to_equal(35)  # oracle: pinned constant asserted by this scenario
expect(small.max_y).to_equal(24)  # oracle: pinned constant asserted by this scenario
expect(small.first_x).to_equal(11)  # oracle: pinned constant asserted by this scenario
expect(small.first_y).to_equal(14)  # oracle: pinned constant asserted by this scenario
expect(small.first_pixel).to_equal(4282268725u32)
expect(small.corner_pixel).to_equal(rgb(3, 7, 11))
expect(small.last_pixel).to_equal(rgb(3, 7, 11))
expect(large.checksum).to_equal(106035644)  # oracle: pinned constant asserted by this scenario
expect(large.painted).to_equal(334)  # oracle: pinned constant asserted by this scenario
expect(large.partial).to_equal(216)  # oracle: pinned constant asserted by this scenario
expect(large.min_x).to_equal(8)  # oracle: pinned constant asserted by this scenario
expect(large.min_y).to_equal(20)  # oracle: pinned constant asserted by this scenario
expect(large.max_x).to_equal(63)  # oracle: pinned constant asserted by this scenario
expect(large.max_y).to_equal(40)  # oracle: pinned constant asserted by this scenario
expect(capture_current_frame(engine, PRIMARY_CAPTURE)).to_be(true)
engine.unload_font()
engine.shutdown()
```

</details>

#### should reuse every repeated glyph without rerasterization

**Manual warnings:**
- invalid manual visibility metadata: # @manual_section: Warm cache (expected show, folded, detail, or skip)


- Verify: should reuse every repeated glyph without rerasterization
- Load a vector font fixture
- Render the same text again
- Verify cache and performance evidence
   - Expected: cold.checksum equals `warm.checksum`
   - Expected: after.hits - before.hits equals `7)  # oracle: pinned constant asserted by this scenario`
   - Expected: after.misses - before.misses equals `0)  # oracle: pinned constant asserted by this scenario`
   - Expected: after.rasterizations - before.rasterizations equals `0)  # oracle: pinned constant asserted by this scenario`
   - Expected: after.entries equals `before.entries`
   - Expected: after.bytes equals `before.bytes`
   - Expected: after.evictions equals `before.evictions`


<details>
<summary>Executable SSpec</summary>

Runnable source: 28 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-010 REQ-002 REQ-003 REQ-006 REQ-001 REQ-005 REQ-007
step("Verify: should reuse every repeated glyph without rerasterization")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
"""A repeated draw reuses every positioned glyph and performs no new rasterization."""
step("Load a vector font fixture")
expect(materialize_vector_font_fixtures()).to_be(true)
var engine = Engine2D.create_with_backend(128, 72, "cpu")
engine.unload_font()
expect(load_vector_font_fixture(engine, ASCII_FONT)).to_be(true)

step("Render the same text again")
val cold = render_font_fixture(engine, "A A A A", 24)
val before = engine.font_cache_stats()
val warm = render_font_fixture(engine, "A A A A", 24)
val after = engine.font_cache_stats()

step("Verify cache and performance evidence")
expect(cold.checksum).to_equal(warm.checksum)
expect(after.hits - before.hits).to_equal(7)  # oracle: pinned constant asserted by this scenario
expect(after.misses - before.misses).to_equal(0)  # oracle: pinned constant asserted by this scenario
expect(after.rasterizations - before.rasterizations).to_equal(0)  # oracle: pinned constant asserted by this scenario
expect(after.entries).to_equal(before.entries)
expect(after.bytes).to_equal(before.bytes)
expect(after.evictions).to_equal(before.evictions)
expect(after.entries).to_be_less_than(513)
expect(after.bytes).to_be_less_than(33554433)
engine.unload_font()
engine.shutdown()
```

</details>

<details>
<summary>Advanced: should render a directly mapped Latin-1 glyph and a missing-glyph fallback</summary>

#### should render a directly mapped Latin-1 glyph and a missing-glyph fallback

**Manual warnings:**
- invalid manual visibility metadata: # @manual_section: Unicode and fallback (expected show, folded, detail, or skip)


- Verify: should render a directly mapped Latin-1 glyph and a missing-glyph fallback
- Load a vector font fixture
- Render text through the Simple 2D facade
- Verify glyph layout and pixels
   - Expected: latin1.checksum equals `2027554228)  # oracle: pinned constant asserted by this scenario`
   - Expected: latin1.min_x equals `8)  # oracle: pinned constant asserted by this scenario`
   - Expected: latin1.min_y equals `17)  # oracle: pinned constant asserted by this scenario`
   - Expected: latin1.max_x equals `33)  # oracle: pinned constant asserted by this scenario`
   - Expected: latin1.max_y equals `32)  # oracle: pinned constant asserted by this scenario`
   - Expected: fallback.checksum equals `306686342)  # oracle: pinned constant asserted by this scenario`
   - Expected: fallback.painted equals `30)  # oracle: pinned constant asserted by this scenario`
   - Expected: fallback.partial equals `0)  # oracle: pinned constant asserted by this scenario`


<details>
<summary>Executable SSpec</summary>

Runnable source: 27 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-010 REQ-002 REQ-003 REQ-006 REQ-004 REQ-007
step("Verify: should render a directly mapped Latin-1 glyph and a missing-glyph fallback")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
"""A simple-script Unicode mapping uses the selected face while an absent glyph stays visible."""
step("Load a vector font fixture")
expect(materialize_vector_font_fixtures()).to_be(true)
var engine = Engine2D.create_with_backend(128, 72, "cpu")
engine.unload_font()
expect(load_vector_font_fixture(engine, LATIN1_FONT)).to_be(true)

step("Render text through the Simple 2D facade")
val latin1 = render_font_fixture(engine, "éé", 24)
val fallback = render_font_fixture(engine, "Z", 24)

step("Verify glyph layout and pixels")
expect_antialiased_font_pixels(latin1)
expect_nonblank_font_pixels(fallback)
expect(latin1.checksum).to_equal(2027554228)  # oracle: pinned constant asserted by this scenario
expect(latin1.min_x).to_equal(8)  # oracle: pinned constant asserted by this scenario
expect(latin1.min_y).to_equal(17)  # oracle: pinned constant asserted by this scenario
expect(latin1.max_x).to_equal(33)  # oracle: pinned constant asserted by this scenario
expect(latin1.max_y).to_equal(32)  # oracle: pinned constant asserted by this scenario
expect(fallback.checksum).to_equal(306686342)  # oracle: pinned constant asserted by this scenario
expect(fallback.painted).to_equal(30)  # oracle: pinned constant asserted by this scenario
expect(fallback.partial).to_equal(0)  # oracle: pinned constant asserted by this scenario
engine.unload_font()
engine.shutdown()
```

</details>


</details>

#### should preserve the selected face after invalid input and restore bitmap default

**Manual warnings:**
- invalid manual visibility metadata: # @manual_section: Failure safety (expected show, folded, detail, or skip)


- Verify: should preserve the selected face after invalid input and restore bitmap default
- Load a vector font fixture
   - Expected: selected.checksum equals `2027554228)  # oracle: pinned constant asserted by this scenario`
- Reject invalid font input
   - Expected: invalid_size.painted equals `0)  # oracle: pinned constant asserted by this scenario`
   - Expected: after_invalid.generation equals `before_invalid.generation`
   - Expected: after_invalid.entries equals `before_invalid.entries`
   - Expected: after_invalid.bytes equals `before_invalid.bytes`
   - Expected: after_invalid.hits equals `before_invalid.hits`
   - Expected: after_invalid.misses equals `before_invalid.misses`
   - Expected: after_invalid.rasterizations equals `before_invalid.rasterizations`
   - Expected: after_invalid.evictions equals `before_invalid.evictions`
   - Expected: preserved.checksum equals `selected.checksum`
   - Expected: bitmap.checksum equals `104415593)  # oracle: pinned constant asserted by this scenario`
   - Expected: bitmap.painted equals `324)  # oracle: pinned constant asserted by this scenario`
   - Expected: bitmap.partial equals `0)  # oracle: pinned constant asserted by this scenario`


<details>
<summary>Executable SSpec</summary>

Runnable source: 38 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-010 REQ-002 REQ-003 REQ-004 REQ-001 REQ-005 REQ-007
step("Verify: should preserve the selected face after invalid input and restore bitmap default")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
"""Rejected paths never replace the active face, and unload returns to bitmap text."""
step("Load a vector font fixture")
expect(materialize_vector_font_fixtures()).to_be(true)
var engine = Engine2D.create_with_backend(128, 72, "cpu")
engine.unload_font()
expect(load_vector_font_fixture(engine, ASCII_FONT)).to_be(true)
val selected = render_font_fixture(engine, "AA", 24)
expect(selected.checksum).to_equal(2027554228)  # oracle: pinned constant asserted by this scenario
val before_invalid = engine.font_cache_stats()

step("Reject invalid font input")
expect(engine.load_font("")).to_be(false)
expect(engine.load_font(FIXTURE_DIR + "/missing.ttf")).to_be(false)
expect(engine.load_font(MALFORMED_FONT)).to_be(false)
expect(engine.load_font(UNSUPPORTED_FONT)).to_be(false)
val invalid_size = render_font_fixture(engine, "A", 513)
expect(invalid_size.painted).to_equal(0)  # oracle: pinned constant asserted by this scenario
val after_invalid = engine.font_cache_stats()
expect(after_invalid.generation).to_equal(before_invalid.generation)
expect(after_invalid.entries).to_equal(before_invalid.entries)
expect(after_invalid.bytes).to_equal(before_invalid.bytes)
expect(after_invalid.hits).to_equal(before_invalid.hits)
expect(after_invalid.misses).to_equal(before_invalid.misses)
expect(after_invalid.rasterizations).to_equal(before_invalid.rasterizations)
expect(after_invalid.evictions).to_equal(before_invalid.evictions)
val preserved = render_font_fixture(engine, "AA", 24)
expect(preserved.checksum).to_equal(selected.checksum)

engine.unload_font()
val bitmap = render_font_fixture(engine, "AA", 24)
expect_nonblank_font_pixels(bitmap)
expect(bitmap.checksum).to_equal(104415593)  # oracle: pinned constant asserted by this scenario
expect(bitmap.painted).to_equal(324)  # oracle: pinned constant asserted by this scenario
expect(bitmap.partial).to_equal(0)  # oracle: pinned constant asserted by this scenario
engine.shutdown()
```

</details>

<details>
<summary>Advanced: should invalidate cached glyphs when another face is selected</summary>

#### should invalidate cached glyphs when another face is selected

**Manual warnings:**
- invalid manual visibility metadata: # @manual_section: Cache invalidation (expected show, folded, detail, or skip)


- Verify: should invalidate cached glyphs when another face is selected
- Load a vector font fixture
   - Expected: replaced.entries equals `0)  # oracle: pinned constant asserted by this scenario`


<details>
<summary>Executable SSpec</summary>

Runnable source: 20 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-010 REQ-002 REQ-003 REQ-006 REQ-004 REQ-001 REQ-005
step("Verify: should invalidate cached glyphs when another face is selected")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
"""Successful face replacement drops prior glyph entries and advances native generation."""
step("Load a vector font fixture")
expect(materialize_vector_font_fixtures()).to_be(true)
var engine = Engine2D.create_with_backend(128, 72, "cpu")
expect(engine.load_font(ASCII_FONT)).to_be(true)
render_font_fixture(engine, "AA", 24)
val first = engine.font_cache_stats()
expect(first.entries).to_be_greater_than(0)

expect(engine.load_font(LATIN1_FONT)).to_be(true)
val replaced = engine.font_cache_stats()
expect(replaced.entries).to_equal(0)  # oracle: pinned constant asserted by this scenario
render_font_fixture(engine, "éé", 24)
val second = engine.font_cache_stats()
expect(second.generation).to_be_greater_than(first.generation)
expect(second.entries).to_be_greater_than(0)
engine.shutdown()
```

</details>


</details>

<details>
<summary>Advanced: should keep bitmap text as the default before font selection</summary>

#### should keep bitmap text as the default before font selection

**Manual warnings:**
- invalid manual visibility metadata: # @manual_section: Bitmap default (expected show, folded, detail, or skip)


- Verify: should keep bitmap text as the default before font selection
   - Expected: bitmap.checksum equals `104415593)  # oracle: pinned constant asserted by this scenario`
   - Expected: bitmap.min_x equals `8)  # oracle: pinned constant asserted by this scenario`
   - Expected: bitmap.min_y equals `8)  # oracle: pinned constant asserted by this scenario`
   - Expected: bitmap.max_x equals `37)  # oracle: pinned constant asserted by this scenario`
   - Expected: bitmap.max_y equals `28)  # oracle: pinned constant asserted by this scenario`
   - Expected: stats.entries equals `0)  # oracle: pinned constant asserted by this scenario`


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-010 REQ-002 REQ-006 REQ-004 REQ-001 REQ-005 REQ-007
step("Verify: should keep bitmap text as the default before font selection")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
"""A new engine renders visible bitmap text without loading a vector face."""
var engine = Engine2D.create_with_backend(128, 72, "cpu")
val bitmap = render_font_fixture(engine, "AA", 24)
expect_nonblank_font_pixels(bitmap)
expect(bitmap.checksum).to_equal(104415593)  # oracle: pinned constant asserted by this scenario
expect(bitmap.min_x).to_equal(8)  # oracle: pinned constant asserted by this scenario
expect(bitmap.min_y).to_equal(8)  # oracle: pinned constant asserted by this scenario
expect(bitmap.max_x).to_equal(37)  # oracle: pinned constant asserted by this scenario
expect(bitmap.max_y).to_equal(28)  # oracle: pinned constant asserted by this scenario
val stats = engine.font_cache_stats()
expect(stats.entries).to_equal(0)  # oracle: pinned constant asserted by this scenario
engine.shutdown()
```

</details>


</details>

<details>
<summary>Advanced: should clip selected vector text at the viewport boundary</summary>

#### should clip selected vector text at the viewport boundary

**Manual warnings:**
- invalid manual visibility metadata: # @manual_section: Clipping (expected show, folded, detail, or skip)


- Verify: should clip selected vector text at the viewport boundary
- Load a vector font fixture
- Render text through the Simple 2D facade
- Verify glyph layout and pixels
   - Expected: clipped.checksum equals `1011943063)  # oracle: pinned constant asserted by this scenario`
   - Expected: clipped.painted equals `181)  # oracle: pinned constant asserted by this scenario`
   - Expected: clipped.partial equals `134)  # oracle: pinned constant asserted by this scenario`
   - Expected: clipped.min_x equals `0)  # oracle: pinned constant asserted by this scenario`
   - Expected: clipped.min_y equals `5)  # oracle: pinned constant asserted by this scenario`
   - Expected: clipped.max_x equals `36)  # oracle: pinned constant asserted by this scenario`
   - Expected: clipped.max_y equals `20)  # oracle: pinned constant asserted by this scenario`
   - Expected: clipped.last_pixel equals `rgb(3, 7, 11)`


<details>
<summary>Executable SSpec</summary>

Runnable source: 22 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-010 REQ-002 REQ-003 REQ-006 REQ-004 REQ-001 REQ-005 REQ-007
step("Verify: should clip selected vector text at the viewport boundary")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
"""Negative draw coordinates clip pixels without changing the glyph layout."""
step("Load a vector font fixture")
expect(materialize_vector_font_fixtures()).to_be(true)
var engine = Engine2D.create_with_backend(128, 72, "cpu")
expect(engine.load_font(ASCII_FONT)).to_be(true)

step("Render text through the Simple 2D facade")
val clipped = render_font_fixture_at(engine, "A A", 24, -4, -4)

step("Verify glyph layout and pixels")
expect(clipped.checksum).to_equal(1011943063)  # oracle: pinned constant asserted by this scenario
expect(clipped.painted).to_equal(181)  # oracle: pinned constant asserted by this scenario
expect(clipped.partial).to_equal(134)  # oracle: pinned constant asserted by this scenario
expect(clipped.min_x).to_equal(0)  # oracle: pinned constant asserted by this scenario
expect(clipped.min_y).to_equal(5)  # oracle: pinned constant asserted by this scenario
expect(clipped.max_x).to_equal(36)  # oracle: pinned constant asserted by this scenario
expect(clipped.max_y).to_equal(20)  # oracle: pinned constant asserted by this scenario
expect(clipped.last_pixel).to_equal(rgb(3, 7, 11))
engine.shutdown()
```

</details>


</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 7 |
| Active scenarios | 7 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `28ff4d79f8cce9723940ceac938d9ab732d0f6bb89b03db5de8404efa54ac8ce`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `28ff4d79f8cce9723940ceac938d9ab732d0f6bb89b03db5de8404efa54ac8ce`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `28ff4d79f8cce9723940ceac938d9ab732d0f6bb89b03db5de8404efa54ac8ce`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **90/100**; effective score: **90/100**; blockers: **0**.

SSpec documentization score: 90/100
source: test/03_system/app/simple_2d/feature/simple_2d_vector_fonts_spec.spl
mirror: doc/06_spec/03_system/app/simple_2d/feature/simple_2d_vector_fonts_spec.md (current)
findings: 9 blockers: 0
  narrative=100 structure=70 oracle=100
  traceability=100 evidence=85 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/03_system/app/simple_2d/feature/simple_2d_vector_fonts_spec.md:1:1: warning SSDOC-EVD-002 [evidence] (-15): source steps are not visible in the generated manual
  why: Source tokens alone do not prove reader-visible workflow structure.
  improve: Use supported literal step calls and regenerate the manual.
doc/06_spec/03_system/app/simple_2d/feature/simple_2d_vector_fonts_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/app/simple_2d/feature/simple_2d_vector_fonts_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: assumptions/preconditions, traceability, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/app/simple_2d/feature/simple_2d_vector_fonts_spec.spl:140:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should render a selected ASCII vector font at two sizes' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/03_system/app/simple_2d/feature/simple_2d_vector_fonts_spec.spl:184:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should reuse every repeated glyph without rerasterization' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/03_system/app/simple_2d/feature/simple_2d_vector_fonts_spec.spl:217:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should render a directly mapped Latin-1 glyph and a missing-glyph fallback' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/03_system/app/simple_2d/feature/simple_2d_vector_fonts_spec.spl:250:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should preserve the selected face after invalid input and restore bitmap default' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/03_system/app/simple_2d/feature/simple_2d_vector_fonts_spec.spl:293:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should invalidate cached glyphs when another face is selected' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/03_system/app/simple_2d/feature/simple_2d_vector_fonts_spec.spl:318:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should keep bitmap text as the default before font selection' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
<!-- sspec-maintain:scorecard:end -->
