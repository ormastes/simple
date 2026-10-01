# Pseudo Text Wpt Specification

> Tests covering WPT-derived pseudo-element and text shaping.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 15 | 15 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Pseudo Text Wpt Specification

## Scenarios

### WPT-derived pseudo-element and text shaping

#### before pseudo-element content

<details>
<summary>Advanced: renders before pseudo-element content text on empty div</summary>

#### renders before pseudo-element content text on empty div _(slow)_

- renders before pseudo-element content text on empty div
   - Expected: _renders_color(style, body, 0xFF2563EBu32) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("renders before pseudo-element content text on empty div")
val style = "div { color: #2563eb; } div::before { content: 'Hello'; }"
val body = "<div></div>"
expect(_renders_color(style, body, 0xFF2563EBu32)).to_equal(true)
```

</details>


</details>

<details>
<summary>Advanced: renders before pseudo-element on empty element</summary>

#### renders before pseudo-element on empty element _(slow)_

- renders before pseudo-element on empty element
   - Expected: _renders_color(style, body, 0xFF16A34Au32) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("renders before pseudo-element on empty element")
val style = "div { color: #16a34a; } div::before { content: 'Generated'; }"
val body = "<div></div>"
expect(_renders_color(style, body, 0xFF16A34Au32)).to_equal(true)
```

</details>


</details>

<details>
<summary>Advanced: renders before pseudo-element attr content</summary>

#### renders before pseudo-element attr content _(slow)_

- renders before pseudo-element attr content
   - Expected: _pixel_count(style, body, 0xFF2563EBu32) equals `96`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("renders before pseudo-element attr content")
val style = "div { color: #2563eb; font-size: 8px; } div::before { content: attr(data-label); }"
val body = "<div data-label='ABC'></div>"
expect(_pixel_count(style, body, 0xFF2563EBu32)).to_equal(96)
```

</details>


</details>

#### after pseudo-element content

<details>
<summary>Advanced: renders after pseudo-element content text on empty div</summary>

#### renders after pseudo-element content text on empty div _(slow)_

- renders after pseudo-element content text on empty div
   - Expected: _renders_color(style, body, 0xFFDC2626u32) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("renders after pseudo-element content text on empty div")
val style = "div { color: #dc2626; } div::after { content: 'Suffix'; }"
val body = "<div></div>"
expect(_renders_color(style, body, 0xFFDC2626u32)).to_equal(true)
```

</details>


</details>

<details>
<summary>Advanced: renders after pseudo-element on empty element</summary>

#### renders after pseudo-element on empty element _(slow)_

- renders after pseudo-element on empty element
   - Expected: _renders_color(style, body, 0xFF7C3AEDu32) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("renders after pseudo-element on empty element")
val style = "div { color: #7c3aed; } div::after { content: 'Only'; }"
val body = "<div></div>"
expect(_renders_color(style, body, 0xFF7C3AEDu32)).to_equal(true)
```

</details>


</details>

<details>
<summary>Advanced: renders after pseudo-element attr content</summary>

#### renders after pseudo-element attr content _(slow)_

- renders after pseudo-element attr content
   - Expected: _pixel_count(style, body, 0xFFDC2626u32) equals `64`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("renders after pseudo-element attr content")
val style = "div { color: #dc2626; font-size: 8px; } div::after { content: attr(data-label); }"
val body = "<div data-label='XY'></div>"
expect(_pixel_count(style, body, 0xFFDC2626u32)).to_equal(64)
```

</details>


</details>

<details>
<summary>Advanced: keeps missing attr pseudo content empty</summary>

#### keeps missing attr pseudo content empty _(slow)_

- keeps missing attr pseudo content empty
   - Expected: _renders_color(style, body, 0xFFDC2626u32) is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("keeps missing attr pseudo content empty")
val style = "div { color: #dc2626; font-size: 8px; } div::after { content: attr(data-label); }"
val body = "<div></div>"
expect(_renders_color(style, body, 0xFFDC2626u32)).to_equal(false)
```

</details>


</details>

<details>
<summary>Advanced: renders both before and after pseudo-elements on empty div</summary>

#### renders both before and after pseudo-elements on empty div _(slow)_

- renders both before and after pseudo-elements on empty div
   - Expected: _renders_color(style, body, 0xFF0891B2u32) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("renders both before and after pseudo-elements on empty div")
val style = "div { color: #0891b2; } div::before { content: 'A'; } div::after { content: 'Z'; }"
val body = "<div></div>"
expect(_renders_color(style, body, 0xFF0891B2u32)).to_equal(true)
```

</details>


</details>

<details>
<summary>Advanced: does not render generated content for display none element</summary>

#### does not render generated content for display none element _(slow)_

- does not render generated content for display none element
   - Expected: _renders_color(style, body, 0xFF0891B2u32) is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("does not render generated content for display none element")
val style = "div { display: none; color: #0891b2; } div::before { content: 'Hidden'; }"
val body = "<div></div>"
expect(_renders_color(style, body, 0xFF0891B2u32)).to_equal(false)
```

</details>


</details>

<details>
<summary>Advanced: does not render generated content when pseudo display is none</summary>

#### does not render generated content when pseudo display is none _(slow)_

- does not render generated content when pseudo display is none
   - Expected: _renders_color(style, body, 0xFF0891B2u32) is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("does not render generated content when pseudo display is none")
val style = "div { color: #0891b2; } div::before { content: 'Hidden'; display: none; }"
val body = "<div></div>"
expect(_renders_color(style, body, 0xFF0891B2u32)).to_equal(false)
```

</details>


</details>

#### text-overflow ellipsis

<details>
<summary>Advanced: truncates overflowing text with ellipsis</summary>

#### truncates overflowing text with ellipsis _(slow)_

- truncates overflowing text with ellipsis


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("truncates overflowing text with ellipsis")
val trunc_style = "div { width: 40px; overflow: hidden; white-space: nowrap; text-overflow: ellipsis; color: #0f766e; font-size: 8px; }"
val no_trunc_style = "div { width: 40px; color: #0f766e; font-size: 8px; }"
val body = "<div>ThisIsAVeryLongWordThatOverflows</div>"
val trunc_px = _pixel_count(trunc_style, body, 0xFF0F766Eu32)
val no_trunc_px = _pixel_count(no_trunc_style, body, 0xFF0F766Eu32)
expect(trunc_px).to_be_less_than(no_trunc_px)
```

</details>


</details>

#### word-break and overflow-wrap

<details>
<summary>Advanced: break-all wraps long word onto second line</summary>

#### break-all wraps long word onto second line _(slow)_

- break-all wraps long word onto second line
   - Expected: _has_color_at_row(style, body, 0xFF4338CAu32, second_row) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("break-all wraps long word onto second line")
val style = "div { width: 40px; word-break: break-all; color: #4338ca; font-size: 8px; }"
val body = "<div>ABCDEFGHIJKLMNOPQRST</div>"
val second_row = 8 + 4 + 2
expect(_has_color_at_row(style, body, 0xFF4338CAu32, second_row)).to_equal(true)
```

</details>


</details>

<details>
<summary>Advanced: overflow-wrap break-word wraps long word onto second line</summary>

#### overflow-wrap break-word wraps long word onto second line _(slow)_

- overflow-wrap break-word wraps long word onto second line
   - Expected: _has_color_at_row(style, body, 0xFF9333EAu32, second_row) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("overflow-wrap break-word wraps long word onto second line")
val style = "div { width: 40px; overflow-wrap: break-word; color: #9333ea; font-size: 8px; }"
val body = "<div>ABCDEFGHIJKLMNOPQRST</div>"
val second_row = 8 + 4 + 2
expect(_has_color_at_row(style, body, 0xFF9333EAu32, second_row)).to_equal(true)
```

</details>


</details>

#### text-align fallback rendering

<details>
<summary>Advanced: centers short text within the fallback block width</summary>

#### centers short text within the fallback block width _(slow)_

- centers short text within the fallback block width
   - Expected: _has_color_at(style, body, 0xFFEA580Cu32, 15, 2) is true
   - Expected: _has_color_at(style, body, 0xFFEA580Cu32, 0, 2) is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("centers short text within the fallback block width")
val style = "div { width: 40px; text-align: center; color: #ea580c; font-size: 8px; }"
val body = "<div>AB</div>"
expect(_has_color_at(style, body, 0xFFEA580Cu32, 15, 2)).to_equal(true)
expect(_has_color_at(style, body, 0xFFEA580Cu32, 0, 2)).to_equal(false)
```

</details>


</details>

<details>
<summary>Advanced: right aligns short text within the fallback block width</summary>

#### right aligns short text within the fallback block width _(slow)_

- right aligns short text within the fallback block width
   - Expected: _has_color_at(style, body, 0xFF0D9488u32, 30, 2) is true
   - Expected: _has_color_at(style, body, 0xFF0D9488u32, 0, 2) is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("right aligns short text within the fallback block width")
val style = "div { width: 40px; text-align: right; color: #0d9488; font-size: 8px; }"
val body = "<div>AB</div>"
expect(_has_color_at(style, body, 0xFF0D9488u32, 30, 2)).to_equal(true)
expect(_has_color_at(style, body, 0xFF0D9488u32, 0, 2)).to_equal(false)
```

</details>


</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/feature/web_platform/css/pseudo_text_wpt_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering WPT-derived pseudo-element and text shaping.
- WPT-derived pseudo-element and text shaping

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 15 |
| Active scenarios | 15 |
| Slow scenarios | 15 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-FEATURE`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `8be00da4a1e8a069d03eaa970cd8ace78b9b21a2b5230d565d26c8801b7c04ab`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `8be00da4a1e8a069d03eaa970cd8ace78b9b21a2b5230d565d26c8801b7c04ab`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `8be00da4a1e8a069d03eaa970cd8ace78b9b21a2b5230d565d26c8801b7c04ab`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **88/100**; effective score: **88/100**; blockers: **0**.

SSpec documentization score: 88/100
source: test/feature/web_platform/css/pseudo_text_wpt_spec.spl
mirror: doc/06_spec/feature/web_platform/css/pseudo_text_wpt_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=80
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/feature/web_platform/css/pseudo_text_wpt_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/feature/web_platform/css/pseudo_text_wpt_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/feature/web_platform/css/pseudo_text_wpt_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-20): 2 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/feature/web_platform/css/pseudo_text_wpt_spec.spl:69:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'renders before pseudo-element content text on empty div' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/feature/web_platform/css/pseudo_text_wpt_spec.spl:76:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'renders before pseudo-element on empty element' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/feature/web_platform/css/pseudo_text_wpt_spec.spl:83:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'renders before pseudo-element attr content' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
