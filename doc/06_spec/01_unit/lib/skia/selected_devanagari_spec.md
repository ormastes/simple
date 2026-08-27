# Selected Devanagari Shaping

> Proves the pinned Noto Sans and Serif Devanagari faces shape the selected Hindi

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 2 | 2 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Selected Devanagari Shaping

Proves the pinned Noto Sans and Serif Devanagari faces shape the selected Hindi

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/skia/selected_devanagari_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

Proves the pinned Noto Sans and Serif Devanagari faces shape the selected Hindi
witnesses to the exact HarfBuzz oracles. The Sans case also rejects font-data drift.

## Scenarios

### selected Hindi dev2 shaping

#### should match the HarfBuzz oracle and reject bound OpenType blob drift

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- should match the HarfBuzz oracle and reject bound OpenType blob drift
- Shape selected Unicode scripts with the pinned face


<details>
<summary>Executable SSpec</summary>

Runnable source: 60 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("should match the HarfBuzz oracle and reject bound OpenType blob drift")
step("Shape selected Unicode scripts with the pinned face")
val path = "assets/fonts/google-fonts/ofl/notosansdevanagari/NotoSansDevanagari[wdth,wght].ttf"
val loaded = load_font(path)
if loaded == nil: fail("Noto Sans Devanagari did not load")
val handle = loaded.?
val parsed = parse_offset_table(file_read_bytes(path)).unwrap()
val font = sk_font_new(sk_typeface_from_attached_font("Noto Sans Devanagari", sk_font_style_normal(), path, handle.handle), 32.0)
val codepoints = [2361u32, 2367u32, 2344u32, 2381u32, 2342u32, 2368u32]
val bound = shaper_with_ot_face(shaper_new(fallback_chain_new(font)), handle.handle, parsed)
val run = shaper_shape_with_language(bound, codepoints, font, 0.0, 0.0, "hi")[0]
expect run.glyph_ids to_equal [544u32, 88u32, 245u32, 73u32, 33u32]
expect run.glyphs[0].x_advance to_equal 8.288
expect run.glyphs[1].x_advance to_equal 16.992
expect run.glyphs[2].x_advance to_equal 9.888
expect run.glyphs[3].x_advance to_equal 16.992
expect run.glyphs[4].x_advance to_equal 8.288
expect run.substitution_complete to_equal true
expect run.positioning_complete to_equal true
expect shaped_run_to_font_glyph_run(run).valid to_equal true

# aalt is available but discretionary. An invalid injected lookup must
# remain unreachable from the default dev2 feature plan.
var discretionary = parse_offset_table(file_read_bytes(path)).unwrap()
val gsub = find_table(discretionary, 1196643650u32).unwrap()
val feature_list = gsub.offset as i64 + read_u16_be(discretionary.blob, gsub.offset as i64 + 6) as i64
val feature_count = read_u16_be(discretionary.blob, feature_list) as i64
var index: i64 = 0
while index < feature_count:
    val record = feature_list + 2 + index * 6
    if read_u32_be(discretionary.blob, record) == 1633774708u32:
        val feature = feature_list + read_u16_be(discretionary.blob, record + 4) as i64
        if read_u16_be(discretionary.blob, feature + 2) > 0u32:
            discretionary.blob[feature + 4] = 255u8
            discretionary.blob[feature + 5] = 255u8
    index = index + 1
val injected = shaper_shape_with_language(
    shaper_with_ot_face(shaper_new(fallback_chain_new(font)), handle.handle, discretionary),
    codepoints, font, 0.0, 0.0, "hi")[0]
expect injected.substitution_complete to_equal false
expect injected.positioning_complete to_equal false
expect shaped_run_to_font_glyph_run(injected).valid to_equal false

var inactive = parse_offset_table(file_read_bytes(path)).unwrap()
val inactive_gsub = find_table(inactive, 1196643650u32).unwrap()
val script_list = inactive_gsub.offset as i64 + read_u16_be(inactive.blob, inactive_gsub.offset as i64 + 4) as i64
val script_count = read_u16_be(inactive.blob, script_list) as i64
index = 0
while index < script_count:
    val record = script_list + 2 + index * 6
    if read_u32_be(inactive.blob, record) == 1684370994u32: inactive.blob[record + 3] = 51u8
    index = index + 1
val rejected = shaper_shape_with_language(
    shaper_with_ot_face(shaper_new(fallback_chain_new(font)), handle.handle, inactive),
    codepoints, font, 0.0, 0.0, "hi")[0]
expect rejected.substitution_complete to_equal false
expect rejected.positioning_complete to_equal false
expect shaped_run_to_font_glyph_run(rejected).valid to_equal false
free_font(handle)
```

</details>

#### should match the Noto Serif Devanagari HarfBuzz oracle

- should match the Noto Serif Devanagari HarfBuzz oracle
- Shape selected Unicode scripts with the pinned face


<details>
<summary>Executable SSpec</summary>

Runnable source: 28 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("should match the Noto Serif Devanagari HarfBuzz oracle")
step("Shape selected Unicode scripts with the pinned face")
val path = "assets/fonts/google-fonts/ofl/notoserifdevanagari/NotoSerifDevanagari[wdth,wght].ttf"
val loaded = load_font(path)
if loaded == nil: fail("Noto Serif Devanagari did not load")
val handle = loaded.?
val parsed = parse_offset_table(file_read_bytes(path)).unwrap()
val font = sk_font_new(sk_typeface_from_attached_font("Noto Serif Devanagari", sk_font_style_normal(), path, handle.handle), 32.0)
val codepoints = [2361u32, 2367u32, 2344u32, 2381u32, 2342u32, 2368u32]
val bound = shaper_with_ot_face(shaper_new(fallback_chain_new(font)), handle.handle, parsed)
val run = shaper_shape_with_language(bound, codepoints, font, 0.0, 0.0, "hi")[0]
expect run.glyph_ids to_equal [557u32, 90u32, 248u32, 75u32, 33u32]
val scale = 32.0 / 1000.0
expect run.glyphs[0].x_advance to_equal 246.0 * scale
expect run.glyphs[1].x_advance to_equal 471.0 * scale
expect run.glyphs[2].x_advance to_equal 283.0 * scale
expect run.glyphs[3].x_advance to_equal 464.0 * scale
expect run.glyphs[4].x_advance to_equal 246.0 * scale
expect run.glyphs[0].cluster to_equal 0
expect run.glyphs[1].cluster to_equal 0
expect run.glyphs[2].cluster to_equal 2
expect run.glyphs[3].cluster to_equal 4
expect run.glyphs[4].cluster to_equal 4
expect run.substitution_complete to_equal true
expect run.positioning_complete to_equal true
expect shaped_run_to_font_glyph_run(run).valid to_equal true
free_font(handle)
```

</details>

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

- Canonical SPipe generation for source `1d605503eb4c16dcea754a7feeef8e64dd6ca74b02d640e1f9c8cc1b31775a0f`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `1d605503eb4c16dcea754a7feeef8e64dd6ca74b02d640e1f9c8cc1b31775a0f`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `1d605503eb4c16dcea754a7feeef8e64dd6ca74b02d640e1f9c8cc1b31775a0f`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/01_unit/lib/skia/selected_devanagari_spec.spl
mirror: doc/06_spec/01_unit/lib/skia/selected_devanagari_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=90 oracle=100
  traceability=100 evidence=80 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/lib/skia/selected_devanagari_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/lib/skia/selected_devanagari_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/lib/skia/selected_devanagari_spec.spl:26:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should match the HarfBuzz oracle and reject bound OpenType blob drift' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/01_unit/lib/skia/selected_devanagari_spec.spl:26:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should match the HarfBuzz oracle and reject bound OpenType blob drift' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/skia/selected_devanagari_spec.spl:89:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should match the Noto Serif Devanagari HarfBuzz oracle' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/01_unit/lib/skia/selected_devanagari_spec.spl:89:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should match the Noto Serif Devanagari HarfBuzz oracle' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
