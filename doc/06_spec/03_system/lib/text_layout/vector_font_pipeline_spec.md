# Vector Font Pipeline (Host)

> End-to-end HOST-side vector font path now used by SimpleOS: the checked-in

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 3 | 3 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Vector Font Pipeline (Host)

End-to-end HOST-side vector font path now used by SimpleOS: the checked-in

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/03_system/lib/text_layout/vector_font_pipeline_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

End-to-end HOST-side vector font path now used by SimpleOS: the checked-in
NotoSansMono selected asset validates against the pinned registry identity,
its sfnt `name` table decodes the five canonical embedded names, and the
pure-sfnt-glyf rasterizer (no native dylib, no dylib_path) turns a real glyph
outline into a nonzero-coverage alpha bitmap. This is the `FontRasterizer`
`lib_handle == 0` branch — `load_selected()` + `rasterize()` routing straight
into `_rasterize_selected_outline()` / `sfnt_rasterize_codepoint_parts()`.

## Scenarios

### Vector font pipeline: selected asset validation

#### selected font asset validates

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- selected font asset validates
- Read the checked-in NotoSansMono selected asset bytes
   - Expected: blob.len() equals `1708408`
- Validate the exact bytes against the pinned registry identity
   - Expected: result.reason equals `valid`
   - Expected: result.family equals `Noto Sans Mono`


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("selected font asset validates")
step("Read the checked-in NotoSansMono selected asset bytes")
val blob = file_read_bytes(NOTO_SANS_MONO_PATH)
expect(blob.len()).to_equal(1708408)

step("Validate the exact bytes against the pinned registry identity")
val result = validate_selected_font_asset(NOTO_SANS_MONO_PATH, blob)
expect(result.selected).to_be(true)
expect(result.valid).to_be(true)
expect(result.reason).to_equal("valid")
expect(result.family).to_equal("Noto Sans Mono")
```

</details>

### Vector font pipeline: sfnt name table decode

#### name table decodes the 5 canonical names

- name table decodes the 5 canonical names
   - Expected: decoded equals `|Noto Sans Mono|Regular|Noto Sans Mono Regular|NotoSansMono-Regular|Version 2... (full value in folded executable source)`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("name table decodes the 5 canonical names")
val blob = file_read_bytes(NOTO_SANS_MONO_PATH)
val decoded = sfnt_debug_selected_names(blob)
expect(decoded).to_equal("|Noto Sans Mono|Regular|Noto Sans Mono Regular|NotoSansMono-Regular|Version 2.014")
```

</details>

### Vector font pipeline: glyf outline rasterization

#### glyf outline rasterizes a real glyph

- glyf outline rasterizes a real glyph
- Load the selected face through the no-dylib pure-sfnt-glyf path
- Rasterize the digit '0' (codepoint 48) at 12px — the clock uses digits


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("glyf outline rasterizes a real glyph")
step("Load the selected face through the no-dylib pure-sfnt-glyf path")
val fr = FontRasterizer.load_selected(NOTO_SANS_MONO_PATH)
expect(fr != nil).to_be(true)
if fr != nil:
    step("Rasterize the digit '0' (codepoint 48) at 12px — the clock uses digits")
    val glyph = fr.rasterize(48, 12)
    expect(glyph != nil).to_be(true)
    if glyph != nil:
        Then_glyph_has_plausible_coverage(glyph)
```

</details>

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

- `REQ-SSPEC-SYSTEM`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `951bfec1b977f8c32a2f4c6e3e0d2953b888d368a27698bf6f5fa688a8e77bad`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `951bfec1b977f8c32a2f4c6e3e0d2953b888d368a27698bf6f5fa688a8e77bad`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `951bfec1b977f8c32a2f4c6e3e0d2953b888d368a27698bf6f5fa688a8e77bad`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **90/100**; effective score: **90/100**; blockers: **0**.

SSpec documentization score: 90/100
source: test/03_system/lib/text_layout/vector_font_pipeline_spec.spl
mirror: doc/06_spec/03_system/lib/text_layout/vector_font_pipeline_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=90
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/03_system/lib/text_layout/vector_font_pipeline_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/lib/text_layout/vector_font_pipeline_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/lib/text_layout/vector_font_pipeline_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-10): 1 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/03_system/lib/text_layout/vector_font_pipeline_spec.spl:54:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'selected font asset validates' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/lib/text_layout/vector_font_pipeline_spec.spl:70:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'name table decodes the 5 canonical names' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/lib/text_layout/vector_font_pipeline_spec.spl:79:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'glyf outline rasterizes a real glyph' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
