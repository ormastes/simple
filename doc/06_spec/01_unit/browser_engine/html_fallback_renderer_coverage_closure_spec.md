# HTML Fallback Renderer — Coverage Closure

> Purpose: Prove that counting and glyph helpers (closure).

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 13 | 13 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# HTML Fallback Renderer — Coverage Closure

Purpose: Prove that counting and glyph helpers (closure).

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/01_unit/browser_engine/html_fallback_renderer_coverage_closure_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Purpose and audience
Purpose: Prove that counting and glyph helpers (closure).
Audience: compiler and tooling engineers who maintain this spec.

## Scenarios

### counting and glyph helpers (closure)

#### counts <div occurrences and returns 0 when absent

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- counts <div occurrences and returns 0 when absent
- Verify: counts <div occurrences and returns 0 when absent
   - Expected: br_count_fallback_divs("<div><div id=x></div></div>") equals `2`
   - Expected: br_count_fallback_divs("<span></span>") equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-BROWSER_ENGINE
step("counts <div occurrences and returns 0 when absent")
step("Verify: counts <div occurrences and returns 0 when absent")
# @req: REQ-BROWSER-ENGINE-HTML-FALLBACK-RENDERER-COVERAGE-CLOSURE-SPEC-SPL-001
expect(br_count_fallback_divs("<div><div id=x></div></div>")).to_equal(2)
expect(br_count_fallback_divs("<span></span>")).to_equal(0)
```

</details>

#### uses a narrower advance for tiny font sizes

- uses a narrower advance for tiny font sizes
- Verify: uses a narrower advance for tiny font sizes
   - Expected: br_char_advance_px(8) equals `5`
   - Expected: br_char_advance_px(16) equals `8`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-BROWSER_ENGINE
step("uses a narrower advance for tiny font sizes")
step("Verify: uses a narrower advance for tiny font sizes")
expect(br_char_advance_px(8)).to_equal(5)  # oracle: 5 — named expected value from the requirement
expect(br_char_advance_px(16)).to_equal(8)  # oracle: 8 — named expected value from the requirement
```

</details>

### br_strip_css_quoted_string (closure)

#### strips matching double and single quotes

- strips matching double and single quotes
- Verify: strips matching double and single quotes
   - Expected: br_strip_css_quoted_string("\"hi\"") equals `hi`
   - Expected: br_strip_css_quoted_string("'hi'") equals `hi`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-BROWSER_ENGINE
step("strips matching double and single quotes")
step("Verify: strips matching double and single quotes")
expect(br_strip_css_quoted_string("\"hi\"")).to_equal("hi")
expect(br_strip_css_quoted_string("'hi'")).to_equal("hi")
```

</details>

#### returns empty for unquoted or too-short values

- returns empty for unquoted or too-short values
- Verify: returns empty for unquoted or too-short values
   - Expected: br_strip_css_quoted_string("hi") equals ``
   - Expected: br_strip_css_quoted_string("'") equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-BROWSER_ENGINE
step("returns empty for unquoted or too-short values")
step("Verify: returns empty for unquoted or too-short values")
expect(br_strip_css_quoted_string("hi")).to_equal("")
expect(br_strip_css_quoted_string("'")).to_equal("")
```

</details>

### ellipsis and wrapping (closure)

#### truncates overflowing text with an ellipsis

- truncates overflowing text with an ellipsis
- Verify: truncates overflowing text with an ellipsis
   - Expected: br_apply_text_overflow_ellipsis("abcdefghij", 40, 16) equals `ab...`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-BROWSER_ENGINE
step("truncates overflowing text with an ellipsis")
step("Verify: truncates overflowing text with an ellipsis")
expect(br_apply_text_overflow_ellipsis("abcdefghij", 40, 16)).to_equal("ab...")
```

</details>

#### returns bare ellipsis for very narrow blocks and passes short text through

- returns bare ellipsis for very narrow blocks and passes short text through
- Verify: returns bare ellipsis for very narrow blocks and passes short text through
   - Expected: br_apply_text_overflow_ellipsis("abcdef", 10, 16) equals `...`
   - Expected: br_apply_text_overflow_ellipsis("ab", 100, 16) equals `ab`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-BROWSER_ENGINE
step("returns bare ellipsis for very narrow blocks and passes short text through")
step("Verify: returns bare ellipsis for very narrow blocks and passes short text through")
expect(br_apply_text_overflow_ellipsis("abcdef", 10, 16)).to_equal("...")
expect(br_apply_text_overflow_ellipsis("ab", 100, 16)).to_equal("ab")
```

</details>

#### wraps only under word-break/overflow-wrap styles

- wraps only under word-break/overflow-wrap styles
- Verify: wraps only under word-break/overflow-wrap styles
   - Expected: br_should_wrap_text("word-break: break-all") is true
   - Expected: br_should_wrap_text("overflow-wrap: break-word") is true
   - Expected: br_should_wrap_text("color: red") is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-BROWSER_ENGINE
step("wraps only under word-break/overflow-wrap styles")
step("Verify: wraps only under word-break/overflow-wrap styles")
expect(br_should_wrap_text("word-break: break-all")).to_equal(true)
expect(br_should_wrap_text("overflow-wrap: break-word")).to_equal(true)
expect(br_should_wrap_text("color: red")).to_equal(false)
```

</details>

#### splits long text into fixed-width lines and leaves short text whole

- splits long text into fixed-width lines and leaves short text whole
- Verify: splits long text into fixed-width lines and leaves short text whole
   - Expected: lines.len() equals `2`
   - Expected: lines[0] equals `abcde`
   - Expected: lines[1] equals `fghij`
   - Expected: br_fallback_wrap_lines("ab", 40, 16).len() equals `1`
   - Expected: br_fallback_wrap_lines("abcdef", 0, 16).len() equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-BROWSER_ENGINE
step("splits long text into fixed-width lines and leaves short text whole")
step("Verify: splits long text into fixed-width lines and leaves short text whole")
val lines = br_fallback_wrap_lines("abcdefghij", 40, 16)
expect(lines.len()).to_equal(2)  # oracle: 2 — named expected value from the requirement
expect(lines[0]).to_equal("abcde")
expect(lines[1]).to_equal("fghij")
expect(br_fallback_wrap_lines("ab", 40, 16).len()).to_equal(1)
expect(br_fallback_wrap_lines("abcdef", 0, 16).len()).to_equal(1)
```

</details>

### tag and div text scanning (closure)

#### reads the first tag's attribute value, empty when tag or attr missing

- reads the first tag's attribute value, empty when tag or attr missing
- Verify: reads the first tag's attribute value, empty when tag or attr missing
   - Expected: br_first_tag_attr_value("<body style=\"margin:0\">", "body", "style") equals `margin:0`
   - Expected: br_first_tag_attr_value("<div></div>", "body", "style") equals ``
   - Expected: br_first_tag_attr_value("<body", "body", "style") equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-BROWSER_ENGINE
step("reads the first tag's attribute value, empty when tag or attr missing")
step("Verify: reads the first tag's attribute value, empty when tag or attr missing")
expect(br_first_tag_attr_value("<body style=\"margin:0\">", "body", "style")).to_equal("margin:0")
expect(br_first_tag_attr_value("<div></div>", "body", "style")).to_equal("")
expect(br_first_tag_attr_value("<body", "body", "style")).to_equal("")
```

</details>

#### extracts direct div text only when no nested markup precedes </div>

- extracts direct div text only when no nested markup precedes </div>
- Verify: extracts direct div text only when no nested markup precedes </div>
   - Expected: br_div_direct_text(html, 5) equals `hello`
   - Expected: br_div_direct_text("<div><span>x</span></div>", 5) equals ``
   - Expected: br_div_direct_text("<div>never closed", 5) equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-BROWSER_ENGINE
step("extracts direct div text only when no nested markup precedes </div>")
step("Verify: extracts direct div text only when no nested markup precedes </div>")
val html = "<div> hello </div>"
expect(br_div_direct_text(html, 5)).to_equal("hello")
expect(br_div_direct_text("<div><span>x</span></div>", 5)).to_equal("")
expect(br_div_direct_text("<div>never closed", 5)).to_equal("")
```

</details>

#### falls back to the first span's text inside the div

- falls back to the first span's text inside the div
- Verify: falls back to the first span's text inside the div
   - Expected: br_div_fallback_text(html, 5) equals `inner`
   - Expected: br_first_span_text_before_div_close(html, 5) equals `inner`
   - Expected: br_first_span_text_before_div_close("<div>plain</div>", 5) equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-BROWSER_ENGINE
step("falls back to the first span's text inside the div")
step("Verify: falls back to the first span's text inside the div")
val html = "<div><span>inner</span></div>"
expect(br_div_fallback_text(html, 5)).to_equal("inner")
expect(br_first_span_text_before_div_close(html, 5)).to_equal("inner")
expect(br_first_span_text_before_div_close("<div>plain</div>", 5)).to_equal("")
```

</details>

### body style defaults (closure)

#### uses inline body style and CSS defaults

- uses inline body style and CSS defaults
- Verify: uses inline body style and CSS defaults
   - Expected: br_body_margin_px("<body style=\"margin:4px\">x</body>") equals `4`
   - Expected: br_body_margin_px("<body>x</body>") equals `8`
   - Expected: br_body_margin_px("<body style=\"margin:-3px\">x</body>") equals `0`
   - Expected: br_body_font_size_px("<body style=\"font-size:20px\">x</body>") equals `20`
   - Expected: br_body_font_size_px("<body>x</body>") equals `16`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-BROWSER_ENGINE
step("uses inline body style and CSS defaults")
step("Verify: uses inline body style and CSS defaults")
expect(br_body_margin_px("<body style=\"margin:4px\">x</body>")).to_equal(4)
expect(br_body_margin_px("<body>x</body>")).to_equal(8)
expect(br_body_margin_px("<body style=\"margin:-3px\">x</body>")).to_equal(0)
expect(br_body_font_size_px("<body style=\"font-size:20px\">x</body>")).to_equal(20)
expect(br_body_font_size_px("<body>x</body>")).to_equal(16)
```

</details>

### br_render_simple_block_fallback_pixels (closure smoke)

#### produces a width*height pixel buffer for simple block markup

- produces a width*height pixel buffer for simple block markup
- Verify: produces a width*height pixel buffer for simple block markup
   - Expected: px.len() equals `128`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-BROWSER_ENGINE
step("produces a width*height pixel buffer for simple block markup")
step("Verify: produces a width*height pixel buffer for simple block markup")
val px = br_render_simple_block_fallback_pixels("<body><div>hi</div></body>", 16, 8)
expect(px.len()).to_equal(128)  # oracle: 128 — named expected value from the requirement
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 13 |
| Active scenarios | 13 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-BROWSER_ENGINE`
- `REQ-BROWSER-ENGINE-HTML-FALLBACK-RENDERER-COVERAGE-CLOSURE-SPEC-SPL-001`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `885f08a61da2376f493592947a287ac2972774b26ad1eba8de4904258925181d`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `885f08a61da2376f493592947a287ac2972774b26ad1eba8de4904258925181d`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `885f08a61da2376f493592947a287ac2972774b26ad1eba8de4904258925181d`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **86/100**; effective score: **86/100**; blockers: **0**.

SSpec documentization score: 86/100
source: test/01_unit/browser_engine/html_fallback_renderer_coverage_closure_spec.spl
mirror: doc/06_spec/01_unit/browser_engine/html_fallback_renderer_coverage_closure_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/browser_engine/html_fallback_renderer_coverage_closure_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/browser_engine/html_fallback_renderer_coverage_closure_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/browser_engine/html_fallback_renderer_coverage_closure_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 9 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/browser_engine/html_fallback_renderer_coverage_closure_spec.spl:47:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'counts <div occurrences and returns 0 when absent' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/browser_engine/html_fallback_renderer_coverage_closure_spec.spl:55:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'uses a narrower advance for tiny font sizes' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/browser_engine/html_fallback_renderer_coverage_closure_spec.spl:63:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'strips matching double and single quotes' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
