# Selected Arabic and Urdu Shaping

> Proves the pinned Noto Naskh Arabic face shapes selected Arabic and Urdu

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 1 | 1 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Selected Arabic and Urdu Shaping

Proves the pinned Noto Naskh Arabic face shapes selected Arabic and Urdu

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/skia/selected_arabic_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

Proves the pinned Noto Naskh Arabic face shapes selected Arabic and Urdu
witnesses to exact HarfBuzz oracles and rejects language, axis, or lookup drift.

## Scenarios

### selected Noto Naskh Arabic shaping

#### should match the HarfBuzz Arabic and Urdu oracles and reject axis or lookup drift

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- should match the HarfBuzz Arabic and Urdu oracles and reject axis or lookup drift
- Shape selected Unicode scripts with the pinned face


<details>
<summary>Executable SSpec</summary>

Runnable source: 88 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("should match the HarfBuzz Arabic and Urdu oracles and reject axis or lookup drift")
step("Shape selected Unicode scripts with the pinned face")
val path = "assets/fonts/google-fonts/ofl/notonaskharabic/NotoNaskhArabic[wght].ttf"
val loaded = load_font(path)
if loaded == nil: fail("Noto Naskh Arabic did not load")
val handle = loaded.?
val parsed = parse_offset_table(file_read_bytes(path)).unwrap()
val font = sk_font_new(sk_typeface_from_attached_font("Noto Naskh Arabic", sk_font_style_normal(), path, handle.handle), 32.0)
val bound = shaper_with_ot_face(shaper_new(fallback_chain_new(font)), handle.handle, parsed)

val arabic_codepoints = [1575u32, 1604u32, 1593u32, 1585u32, 1576u32, 1610u32, 1577u32]
val arabic = shaper_shape_with_language(bound, arabic_codepoints, font, 0.0, 0.0, "ar")[0]
expect arabic.glyph_ids to_equal [294u32, 81u32, 325u32, 18u32, 323u32, 19u32, 29u32, 46u32, 70u32, 8u32]
val scale = 32.0 / 1000.0
val arabic_sources = [6, 6, 5, 5, 4, 4, 3, 2, 1, 0]
val arabic_advances = [0.0 * scale, 452.0 * scale, 0.0 * scale, 360.0 * scale, 0.0 * scale,
    275.0 * scale, 404.0 * scale, 414.0 * scale, 212.0 * scale, 238.0 * scale]
val arabic_x_offsets = [91.0 * scale, 0.0 * scale, 54.0 * scale, 0.0 * scale, 70.0 * scale,
    0.0 * scale, 0.0 * scale, 0.0 * scale, 0.0 * scale, 0.0 * scale]
val arabic_y_offsets = [-294.0 * scale, 0.0 * scale, -17.0 * scale, 0.0 * scale, -31.0 * scale,
    0.0 * scale, 0.0 * scale, 0.0 * scale, 0.0 * scale, 0.0 * scale]
var index: i64 = 0
while index < arabic.glyphs.len():
    expect arabic.glyphs[index].source_index to_equal arabic_sources[index]
    expect arabic.glyphs[index].cluster to_equal arabic_sources[index]
    expect arabic.glyphs[index].x_advance to_equal arabic_advances[index]
    expect arabic.glyphs[index].x_offset to_equal arabic_x_offsets[index]
    expect arabic.glyphs[index].y_offset to_equal arabic_y_offsets[index]
    index = index + 1
expect arabic.substitution_complete to_equal true
expect arabic.positioning_complete to_equal true
expect arabic.is_rtl to_equal true
expect shaped_run_to_font_glyph_run(arabic).valid to_equal true

val urdu_codepoints = [1575u32, 1585u32, 1583u32, 1608u32]
val urdu = shaper_shape_with_language(bound, urdu_codepoints, font, 0.0, 0.0, "ur")[0]
expect urdu.glyph_ids to_equal [94u32, 26u32, 28u32, 8u32]
val urdu_sources = [3, 2, 1, 0]
val urdu_advances = [468.0 * scale, 414.0 * scale, 386.0 * scale, 238.0 * scale]
index = 0
while index < urdu.glyphs.len():
    expect urdu.glyphs[index].source_index to_equal urdu_sources[index]
    expect urdu.glyphs[index].cluster to_equal urdu_sources[index]
    expect urdu.glyphs[index].x_advance to_equal urdu_advances[index]
    expect urdu.glyphs[index].x_offset to_equal 0.0
    expect urdu.glyphs[index].y_offset to_equal 0.0
    index = index + 1
expect urdu.substitution_complete to_equal true
expect urdu.positioning_complete to_equal true
expect urdu.is_rtl to_equal true
expect shaped_run_to_font_glyph_run(urdu).valid to_equal true

val wrong_arabic_language = shaper_shape_with_language(bound, arabic_codepoints, font, 0.0, 0.0, "ur")[0]
expect wrong_arabic_language.substitution_complete to_equal false
expect wrong_arabic_language.positioning_complete to_equal false
expect shaped_run_to_font_glyph_run(wrong_arabic_language).valid to_equal false
val wrong_urdu_language = shaper_shape_with_language(bound, urdu_codepoints, font, 0.0, 0.0, "ar")[0]
expect wrong_urdu_language.substitution_complete to_equal false
expect wrong_urdu_language.positioning_complete to_equal false
expect shaped_run_to_font_glyph_run(wrong_urdu_language).valid to_equal false
val marked = shaper_shape_with_language(bound, [1576u32, 1614u32], font, 0.0, 0.0, "ar")[0]
expect marked.substitution_complete to_equal false
expect marked.positioning_complete to_equal false
expect shaped_run_to_font_glyph_run(marked).valid to_equal false

var wrong_axis = parse_offset_table(file_read_bytes(path)).unwrap()
val fvar = find_table(wrong_axis, 1719034226u32).unwrap()
val axis = fvar.offset as i64 + read_u16_be(wrong_axis.blob, fvar.offset as i64 + 4) as i64
wrong_axis.blob[axis] = 0u8
val wrong_axis_run = shaper_shape_with_language(
    shaper_with_ot_face(shaper_new(fallback_chain_new(font)), handle.handle, wrong_axis),
    arabic_codepoints, font, 0.0, 0.0, "ar")[0]
expect wrong_axis_run.substitution_complete to_equal false
expect wrong_axis_run.positioning_complete to_equal false
expect shaped_run_to_font_glyph_run(wrong_axis_run).valid to_equal false

var wrong_lookup = parse_offset_table(file_read_bytes(path)).unwrap()
val lookups = parse_gsub_skeleton(wrong_lookup)
wrong_lookup.blob[lookups[32].lookup_offset as i64] = 0u8
wrong_lookup.blob[lookups[32].lookup_offset as i64 + 1] = 1u8
val wrong_lookup_run = shaper_shape_with_language(
    shaper_with_ot_face(shaper_new(fallback_chain_new(font)), handle.handle, wrong_lookup),
    arabic_codepoints, font, 0.0, 0.0, "ar")[0]
expect wrong_lookup_run.substitution_complete to_equal false
expect wrong_lookup_run.positioning_complete to_equal false
expect shaped_run_to_font_glyph_run(wrong_lookup_run).valid to_equal false
free_font(handle)
```

</details>

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
- `REQ-007`
- `REQ-014`
- `REQ-SSPEC-LIB`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `a8a7e8eff5a1af5cc3bbf4866297a2e344759dbe5b9443e3d08b487eb3100f15`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `a8a7e8eff5a1af5cc3bbf4866297a2e344759dbe5b9443e3d08b487eb3100f15`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `a8a7e8eff5a1af5cc3bbf4866297a2e344759dbe5b9443e3d08b487eb3100f15`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **88/100**; effective score: **49/100**; blockers: **1**.

SSpec documentization score: 49/100
source: test/01_unit/lib/skia/selected_arabic_spec.spl
mirror: doc/06_spec/01_unit/lib/skia/selected_arabic_spec.md (current)
findings: 5 blockers: 1
  narrative=100 structure=95 oracle=100
  traceability=60 evidence=90 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
  raw=88; blocker cap makes effective=49
doc/06_spec/01_unit/lib/skia/selected_arabic_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/lib/skia/selected_arabic_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/lib/skia/selected_arabic_spec.spl:1:1: blocker SSDOC-TRC-003 [traceability] (-40): 3 declared requirement(s) have no scenario binding
  why: A requirement list without scenario evidence is inventory, not traceability.
  improve: Bind the stable requirement ID inside its executable scenario or explicit blocked case.
test/01_unit/lib/skia/selected_arabic_spec.spl:27:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should match the HarfBuzz Arabic and Urdu oracles and reject axis or lookup drift' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/01_unit/lib/skia/selected_arabic_spec.spl:27:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should match the HarfBuzz Arabic and Urdu oracles and reject axis or lookup drift' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
