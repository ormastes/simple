# Simple 2D Vector Fonts

> Loads deterministic repository-owned TTF fixtures through the public Engine2D

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 7 | 7 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Simple 2D Vector Fonts

Loads deterministic repository-owned TTF fixtures through the public Engine2D

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/03_system/app/simple_2d/feature/simple_2d_vector_fonts_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

Loads deterministic repository-owned TTF fixtures through the public Engine2D
facade, renders real antialiased glyphs, proves warm-cache reuse, preserves the
active face after invalid input, and restores bitmap fallback on unload.

The fixtures derive from ttf-parser's dual MIT/Apache-2.0 400-byte demo font.
The scenarios use the CPU backend at 128x72 and write fixtures below
`build/test-artifacts/03_system/app/simple_2d/feature/simple_2d_vector_fonts`.
The primary flow captures `ascii_32.argb` as 128x72 straight ARGB bytes.
Run the paired timing evidence separately with
`test/05_perf/graphics_2d/simple_2d_vector_fonts_perf_spec.spl`.

## Scenarios

### Simple 2D vector fonts

#### should render a selected ASCII vector font at two sizes

**Manual warnings:**
- invalid manual visibility metadata: # @manual_section: Primary flow (expected show, folded, detail, or skip)


- should render a selected ASCII vector font at two sizes
   - Artifact capture: after_step
- Load a vector font fixture
   - Artifact capture: after_step
- Render text through the Simple 2D facade
   - Artifact capture: after_step
- Verify glyph layout and pixels
   - Artifact capture: after_step
   - Evidence: artifact verified by 19 expected checks
   - Expected: small.checksum equals `160012687`
   - Expected: small.painted equals `106`
   - Expected: small.partial equals `102`
   - Expected: small.min_x equals `8`
   - Expected: small.min_y equals `14`
   - Expected: small.max_x equals `35`
   - Expected: small.max_y equals `24`
   - Expected: small.first_x equals `11`
   - Expected: small.first_y equals `14`
   - Expected: small.first_pixel equals `4282268725u32`
   - Expected: small.corner_pixel equals `rgb(3, 7, 11)`
   - Expected: small.last_pixel equals `rgb(3, 7, 11)`
   - Expected: large.checksum equals `106035644`
   - Expected: large.painted equals `334`
   - Expected: large.partial equals `216`
   - Expected: large.min_x equals `8`
   - Expected: large.min_y equals `20`
   - Expected: large.max_x equals `63`
   - Expected: large.max_y equals `40`


<details>
<summary>Executable SSpec</summary>

Runnable source: 38 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should render a selected ASCII vector font at two sizes")
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
expect(small.checksum).to_equal(160012687)
expect(small.painted).to_equal(106)
expect(small.partial).to_equal(102)
expect(small.min_x).to_equal(8)
expect(small.min_y).to_equal(14)
expect(small.max_x).to_equal(35)
expect(small.max_y).to_equal(24)
expect(small.first_x).to_equal(11)
expect(small.first_y).to_equal(14)
expect(small.first_pixel).to_equal(4282268725u32)
expect(small.corner_pixel).to_equal(rgb(3, 7, 11))
expect(small.last_pixel).to_equal(rgb(3, 7, 11))
expect(large.checksum).to_equal(106035644)
expect(large.painted).to_equal(334)
expect(large.partial).to_equal(216)
expect(large.min_x).to_equal(8)
expect(large.min_y).to_equal(20)
expect(large.max_x).to_equal(63)
expect(large.max_y).to_equal(40)
expect(capture_current_frame(engine, PRIMARY_CAPTURE)).to_be(true)
engine.unload_font()
engine.shutdown()
```

</details>

#### should reuse every repeated glyph without rerasterization

**Manual warnings:**
- invalid manual visibility metadata: # @manual_section: Warm cache (expected show, folded, detail, or skip)


- should reuse every repeated glyph without rerasterization
- Load a vector font fixture
- Render the same text again
- Verify cache and performance evidence
   - Expected: cold.checksum equals `warm.checksum`
   - Expected: after.hits - before.hits equals `7`
   - Expected: after.misses - before.misses equals `0`
   - Expected: after.rasterizations - before.rasterizations equals `0`
   - Expected: after.entries equals `before.entries`
   - Expected: after.bytes equals `before.bytes`
   - Expected: after.evictions equals `before.evictions`


<details>
<summary>Executable SSpec</summary>

Runnable source: 27 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should reuse every repeated glyph without rerasterization")
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
expect(after.hits - before.hits).to_equal(7)
expect(after.misses - before.misses).to_equal(0)
expect(after.rasterizations - before.rasterizations).to_equal(0)
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


- should render a directly mapped Latin-1 glyph and a missing-glyph fallback
- Load a vector font fixture
- Render text through the Simple 2D facade
- Verify glyph layout and pixels
   - Expected: latin1.checksum equals `2027554228`
   - Expected: latin1.min_x equals `8`
   - Expected: latin1.min_y equals `17`
   - Expected: latin1.max_x equals `33`
   - Expected: latin1.max_y equals `32`
   - Expected: fallback.checksum equals `306686342`
   - Expected: fallback.painted equals `30`
   - Expected: fallback.partial equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 26 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should render a directly mapped Latin-1 glyph and a missing-glyph fallback")
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
expect(latin1.checksum).to_equal(2027554228)
expect(latin1.min_x).to_equal(8)
expect(latin1.min_y).to_equal(17)
expect(latin1.max_x).to_equal(33)
expect(latin1.max_y).to_equal(32)
expect(fallback.checksum).to_equal(306686342)
expect(fallback.painted).to_equal(30)
expect(fallback.partial).to_equal(0)
engine.unload_font()
engine.shutdown()
```

</details>


</details>

#### should preserve the selected face after invalid input and restore bitmap default

**Manual warnings:**
- invalid manual visibility metadata: # @manual_section: Failure safety (expected show, folded, detail, or skip)


- should preserve the selected face after invalid input and restore bitmap default
- Load a vector font fixture
   - Expected: selected.checksum equals `2027554228`
- Reject invalid font input
   - Expected: invalid_size.painted equals `0`
   - Expected: after_invalid.generation equals `before_invalid.generation`
   - Expected: after_invalid.entries equals `before_invalid.entries`
   - Expected: after_invalid.bytes equals `before_invalid.bytes`
   - Expected: after_invalid.hits equals `before_invalid.hits`
   - Expected: after_invalid.misses equals `before_invalid.misses`
   - Expected: after_invalid.rasterizations equals `before_invalid.rasterizations`
   - Expected: after_invalid.evictions equals `before_invalid.evictions`
   - Expected: preserved.checksum equals `selected.checksum`
   - Expected: bitmap.checksum equals `104415593`
   - Expected: bitmap.painted equals `324`
   - Expected: bitmap.partial equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 37 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should preserve the selected face after invalid input and restore bitmap default")
"""Rejected paths never replace the active face, and unload returns to bitmap text."""
step("Load a vector font fixture")
expect(materialize_vector_font_fixtures()).to_be(true)
var engine = Engine2D.create_with_backend(128, 72, "cpu")
engine.unload_font()
expect(load_vector_font_fixture(engine, ASCII_FONT)).to_be(true)
val selected = render_font_fixture(engine, "AA", 24)
expect(selected.checksum).to_equal(2027554228)
val before_invalid = engine.font_cache_stats()

step("Reject invalid font input")
expect(engine.load_font("")).to_be(false)
expect(engine.load_font(FIXTURE_DIR + "/missing.ttf")).to_be(false)
expect(engine.load_font(MALFORMED_FONT)).to_be(false)
expect(engine.load_font(UNSUPPORTED_FONT)).to_be(false)
val invalid_size = render_font_fixture(engine, "A", 513)
expect(invalid_size.painted).to_equal(0)
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
expect(bitmap.checksum).to_equal(104415593)
expect(bitmap.painted).to_equal(324)
expect(bitmap.partial).to_equal(0)
engine.shutdown()
```

</details>

<details>
<summary>Advanced: should invalidate cached glyphs when another face is selected</summary>

#### should invalidate cached glyphs when another face is selected

**Manual warnings:**
- invalid manual visibility metadata: # @manual_section: Cache invalidation (expected show, folded, detail, or skip)


- should invalidate cached glyphs when another face is selected
- Load a vector font fixture
   - Expected: replaced.entries equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 19 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should invalidate cached glyphs when another face is selected")
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
expect(replaced.entries).to_equal(0)
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


- should keep bitmap text as the default before font selection
   - Expected: bitmap.checksum equals `104415593`
   - Expected: bitmap.min_x equals `8`
   - Expected: bitmap.min_y equals `8`
   - Expected: bitmap.max_x equals `37`
   - Expected: bitmap.max_y equals `28`
   - Expected: stats.entries equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should keep bitmap text as the default before font selection")
"""A new engine renders visible bitmap text without loading a vector face."""
var engine = Engine2D.create_with_backend(128, 72, "cpu")
val bitmap = render_font_fixture(engine, "AA", 24)
expect_nonblank_font_pixels(bitmap)
expect(bitmap.checksum).to_equal(104415593)
expect(bitmap.min_x).to_equal(8)
expect(bitmap.min_y).to_equal(8)
expect(bitmap.max_x).to_equal(37)
expect(bitmap.max_y).to_equal(28)
val stats = engine.font_cache_stats()
expect(stats.entries).to_equal(0)
engine.shutdown()
```

</details>


</details>

<details>
<summary>Advanced: should clip selected vector text at the viewport boundary</summary>

#### should clip selected vector text at the viewport boundary

**Manual warnings:**
- invalid manual visibility metadata: # @manual_section: Clipping (expected show, folded, detail, or skip)


- should clip selected vector text at the viewport boundary
- Load a vector font fixture
- Render text through the Simple 2D facade
- Verify glyph layout and pixels
   - Expected: clipped.checksum equals `1011943063`
   - Expected: clipped.painted equals `181`
   - Expected: clipped.partial equals `134`
   - Expected: clipped.min_x equals `0`
   - Expected: clipped.min_y equals `5`
   - Expected: clipped.max_x equals `36`
   - Expected: clipped.max_y equals `20`
   - Expected: clipped.last_pixel equals `rgb(3, 7, 11)`


<details>
<summary>Executable SSpec</summary>

Runnable source: 21 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should clip selected vector text at the viewport boundary")
"""Negative draw coordinates clip pixels without changing the glyph layout."""
step("Load a vector font fixture")
expect(materialize_vector_font_fixtures()).to_be(true)
var engine = Engine2D.create_with_backend(128, 72, "cpu")
expect(engine.load_font(ASCII_FONT)).to_be(true)

step("Render text through the Simple 2D facade")
val clipped = render_font_fixture_at(engine, "A A", 24, -4, -4)

step("Verify glyph layout and pixels")
expect(clipped.checksum).to_equal(1011943063)
expect(clipped.painted).to_equal(181)
expect(clipped.partial).to_equal(134)
expect(clipped.min_x).to_equal(0)
expect(clipped.min_y).to_equal(5)
expect(clipped.max_x).to_equal(36)
expect(clipped.max_y).to_equal(20)
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

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-SYSTEM`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `ea3cfd466b8a3d8c2e82e3134aa17eb294c803c22477dcc2b7fab9eba0991bd6`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `ea3cfd466b8a3d8c2e82e3134aa17eb294c803c22477dcc2b7fab9eba0991bd6`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `ea3cfd466b8a3d8c2e82e3134aa17eb294c803c22477dcc2b7fab9eba0991bd6`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **82/100**; effective score: **82/100**; blockers: **0**.

SSpec documentization score: 82/100
source: test/03_system/app/simple_2d/feature/simple_2d_vector_fonts_spec.spl
mirror: doc/06_spec/03_system/app/simple_2d/feature/simple_2d_vector_fonts_spec.md (current)
findings: 12 blockers: 0
  narrative=100 structure=70 oracle=70
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/03_system/app/simple_2d/feature/simple_2d_vector_fonts_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/app/simple_2d/feature/simple_2d_vector_fonts_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/app/simple_2d/feature/simple_2d_vector_fonts_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 46 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/03_system/app/simple_2d/feature/simple_2d_vector_fonts_spec.spl:130:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should render a selected ASCII vector font at two sizes' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/03_system/app/simple_2d/feature/simple_2d_vector_fonts_spec.spl:174:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should reuse every repeated glyph without rerasterization' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/03_system/app/simple_2d/feature/simple_2d_vector_fonts_spec.spl:174:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should reuse every repeated glyph without rerasterization' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/app/simple_2d/feature/simple_2d_vector_fonts_spec.spl:206:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should render a directly mapped Latin-1 glyph and a missing-glyph fallback' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/03_system/app/simple_2d/feature/simple_2d_vector_fonts_spec.spl:206:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should render a directly mapped Latin-1 glyph and a missing-glyph fallback' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/app/simple_2d/feature/simple_2d_vector_fonts_spec.spl:238:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should preserve the selected face after invalid input and restore bitmap default' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/03_system/app/simple_2d/feature/simple_2d_vector_fonts_spec.spl:238:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should preserve the selected face after invalid input and restore bitmap default' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/app/simple_2d/feature/simple_2d_vector_fonts_spec.spl:280:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should invalidate cached glyphs when another face is selected' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/03_system/app/simple_2d/feature/simple_2d_vector_fonts_spec.spl:304:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should keep bitmap text as the default before font selection' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
<!-- sspec-maintain:scorecard:end -->
