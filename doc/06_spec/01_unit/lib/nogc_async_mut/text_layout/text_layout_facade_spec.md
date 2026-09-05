# Text Layout Facade Specification

> Tests covering nogc_async_mut text_layout facades.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 1 | 1 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Text Layout Facade Specification

## Scenarios

### nogc_async_mut text_layout facades

#### re-exports deterministic font metadata and records

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- re-exports deterministic font metadata and records
   - Expected: default_mono_font_name() equals `Noto Sans Mono`
   - Expected: default_mono_font_path() contains `NotoSansMono[wdth,wght].ttf`
   - Expected: vf_glyph_width(65) equals `11`
   - Expected: vf_glyph_commands(65)[0] equals `0`
   - Expected: vf_glyph_commands(65)[vf_glyph_commands(65).len() - 3] equals `3`
   - Expected: browser_font_face_source_from_family_value(family) equals `/tmp/example.ttf`
   - Expected: browser_font_face_local_source_path("'file:///tmp/example.ttf'") equals `/tmp/example.ttf`
   - Expected: browser_font_face_cached_source_path("https://example.test/font.woff2").starts_with(browser_font_cache_dir()) is true
   - Expected: result.status equals `available`
   - Expected: glyph.codepoint equals `65`
   - Expected: glyph.pixels.len() equals `0`
   - Expected: GlyphCache.new(2).max_entries equals `2`
   - Expected: FontRenderer.new().use_vector is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 21 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("re-exports deterministic font metadata and records")
expect(default_mono_font_name()).to_equal("Noto Sans Mono")
expect(default_mono_font_path().contains("NotoSansMono[wdth,wght].ttf")).to_equal(true)
expect(vf_glyph_width(65)).to_equal(11)
expect(vf_glyph_commands(65)[0]).to_equal(0)
expect(vf_glyph_commands(65)[vf_glyph_commands(65).len() - 3]).to_equal(3)

val family = browser_font_face_family_value("Example Sans", "file:///tmp/example.ttf")
expect(browser_font_face_source_from_family_value(family)).to_equal("/tmp/example.ttf")
expect(browser_font_face_local_source_path("'file:///tmp/example.ttf'")).to_equal("/tmp/example.ttf")
expect(browser_font_face_cached_source_path("https://example.test/font.woff2").starts_with(browser_font_cache_dir())).to_equal(true)

val result = BrowserFontMaterializeResult(ok: true, attempted_download: false, status: "available", stdout: "", stderr: "", exit_code: 0)
expect(result.status).to_equal("available")

val glyph = CachedGlyph.empty(65, 24)
expect(glyph.codepoint).to_equal(65)
expect(glyph.pixels.len()).to_equal(0)
expect(GlyphCache.new(2).max_entries).to_equal(2)
expect(FontRenderer.new().use_vector).to_equal(true)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/nogc_async_mut/text_layout/text_layout_facade_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering nogc_async_mut text_layout facades.
- nogc_async_mut text_layout facades

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

- Canonical SPipe generation for source `1788fc0cfd9c938f65cbfd799b9f67003e8e7b32e5501c038d567cf1facbaf02`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `1788fc0cfd9c938f65cbfd799b9f67003e8e7b32e5501c038d567cf1facbaf02`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `1788fc0cfd9c938f65cbfd799b9f67003e8e7b32e5501c038d567cf1facbaf02`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **89/100**; effective score: **89/100**; blockers: **0**.

SSpec documentization score: 89/100
source: test/01_unit/lib/nogc_async_mut/text_layout/text_layout_facade_spec.spl
mirror: doc/06_spec/01_unit/lib/nogc_async_mut/text_layout/text_layout_facade_spec.md (current)
findings: 4 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=90 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/lib/nogc_async_mut/text_layout/text_layout_facade_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/lib/nogc_async_mut/text_layout/text_layout_facade_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/lib/nogc_async_mut/text_layout/text_layout_facade_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 6 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/lib/nogc_async_mut/text_layout/text_layout_facade_spec.spl:15:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 're-exports deterministic font metadata and records' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
