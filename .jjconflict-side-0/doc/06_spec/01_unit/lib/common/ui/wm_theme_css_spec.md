# Wm Theme Css Specification

> Tests covering WM theme CSS/HTML parser.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 7 | 7 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Wm Theme Css Specification

## Scenarios

### WM theme CSS/HTML parser

#### parses all 6 --wm-* custom properties from raw CSS

- parses all 6 --wm-* custom properties from raw CSS
   - Expected: tokens.wtc_bg equals `#112233`
   - Expected: tokens.wtc_fg equals `#445566`
   - Expected: tokens.wtc_accent equals `#778899`
   - Expected: tokens.wtc_surface equals `#aabbcc`
   - Expected: tokens.wtc_surface_hover equals `#ddeeff`
   - Expected: tokens.wtc_error equals `#ff0000`
   - Expected: colors.desktop_bg equals `0xFF112233u32`
   - Expected: colors.text_primary equals `0xFF445566u32`
   - Expected: colors.accent equals `0xFF778899u32`
   - Expected: colors.command_lane equals `0xFFAABBCCu32`
   - Expected: colors.title_unfocused equals `0xFFDDEEFFu32`
   - Expected: colors.close_button equals `0xFFFF0000u32`


<details>
<summary>Executable SSpec</summary>

Runnable source: 18 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("parses all 6 --wm-* custom properties from raw CSS")
val css = "--wm-bg: #112233; --wm-fg: #445566; --wm-accent: #778899; --wm-surface: #aabbcc; --wm-surface-hover: #ddeeff; --wm-error: #ff0000;"
val tokens = wm_theme_tokens_from_css(css)
expect(tokens.wtc_bg).to_equal("#112233")
expect(tokens.wtc_fg).to_equal("#445566")
expect(tokens.wtc_accent).to_equal("#778899")
expect(tokens.wtc_surface).to_equal("#aabbcc")
expect(tokens.wtc_surface_hover).to_equal("#ddeeff")
expect(tokens.wtc_error).to_equal("#ff0000")

val colors = wm_chrome_colors_from_css_text(css)
expect(colors.desktop_bg).to_equal(0xFF112233u32)
expect(colors.text_primary).to_equal(0xFF445566u32)
expect(colors.accent).to_equal(0xFF778899u32)
expect(colors.command_lane).to_equal(0xFFAABBCCu32)
expect(colors.title_unfocused).to_equal(0xFFDDEEFFu32)
expect(colors.close_button).to_equal(0xFFFF0000u32)
```

</details>

#### disambiguates --wm-surface from the longer --wm-surface-hover

- disambiguates --wm-surface from the longer --wm-surface-hover
   - Expected: tokens.wtc_surface equals `#101010`
   - Expected: tokens.wtc_surface_hover equals `#202020`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("disambiguates --wm-surface from the longer --wm-surface-hover")
val css = "--wm-surface: #101010; --wm-surface-hover: #202020;"
val tokens = wm_theme_tokens_from_css(css)
expect(tokens.wtc_surface).to_equal("#101010")
expect(tokens.wtc_surface_hover).to_equal("#202020")
```

</details>

#### extracts tokens from a <style> block inside an HTML document

- extracts tokens from a <style> block inside an HTML document
   - Expected: tokens.wtc_bg equals `#123456`
   - Expected: tokens.wtc_accent equals `#abcdef`
   - Expected: tokens.wtc_fg equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("extracts tokens from a <style> block inside an HTML document")
val html = "<html><head><style>\n  --wm-bg: #123456;\n  --wm-accent: #abcdef;\n</style></head><body></body></html>"
val tokens = wm_theme_tokens_from_html(html)
expect(tokens.wtc_bg).to_equal("#123456")
expect(tokens.wtc_accent).to_equal("#abcdef")
expect(tokens.wtc_fg).to_equal("")
```

</details>

#### falls back to defaults for any missing token

- falls back to defaults for any missing token
   - Expected: colors.desktop_bg equals `defaults.desktop_bg`
   - Expected: colors.close_button equals `defaults.close_button`
   - Expected: colors.command_lane equals `defaults.command_lane`
   - Expected: colors.accent equals `0xFF010203u32`
   - Expected: colors.title_focused equals `0xFF010203u32`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("falls back to defaults for any missing token")
val css = "--wm-accent: #010203;"
val defaults = wm_chrome_theme_defaults()
val colors = wm_chrome_colors_from_css_text(css)
expect(colors.desktop_bg).to_equal(defaults.desktop_bg)
expect(colors.close_button).to_equal(defaults.close_button)
expect(colors.command_lane).to_equal(defaults.command_lane)
expect(colors.accent).to_equal(0xFF010203u32)
expect(colors.title_focused).to_equal(0xFF010203u32)
```

</details>

#### expands 3-digit hex shorthand

- expands 3-digit hex shorthand
   - Expected: tokens.wtc_error equals `#f0a`
   - Expected: colors.close_button equals `0xFFFF00AAu32`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("expands 3-digit hex shorthand")
val css = "--wm-error: #f0a;"
val tokens = wm_theme_tokens_from_css(css)
expect(tokens.wtc_error).to_equal("#f0a")
val colors = wm_chrome_colors_from_css_text(css)
expect(colors.close_button).to_equal(0xFFFF00AAu32)
```

</details>

#### treats garbage input as all-defaults, never a crash

- treats garbage input as all-defaults, never a crash
   - Expected: tokens.wtc_bg equals ``
   - Expected: tokens.wtc_error equals ``
   - Expected: colors.desktop_bg equals `defaults.desktop_bg`
   - Expected: colors.close_button equals `defaults.close_button`
   - Expected: colors.background_hex equals `defaults.background_hex`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("treats garbage input as all-defaults, never a crash")
val defaults = wm_chrome_theme_defaults()
val garbage = "this is not a stylesheet at all { nonsense: yes }"
val tokens = wm_theme_tokens_from_css(garbage)
expect(tokens.wtc_bg).to_equal("")
expect(tokens.wtc_error).to_equal("")
val colors = wm_chrome_colors_from_css_text(garbage)
expect(colors.desktop_bg).to_equal(defaults.desktop_bg)
expect(colors.close_button).to_equal(defaults.close_button)
expect(colors.background_hex).to_equal(defaults.background_hex)
```

</details>

#### treats an empty string as all-defaults

- treats an empty string as all-defaults
   - Expected: colors.desktop_bg equals `defaults.desktop_bg`
   - Expected: colors.accent equals `defaults.accent`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("treats an empty string as all-defaults")
val defaults = wm_chrome_theme_defaults()
val colors = wm_chrome_colors_from_css_text("")
expect(colors.desktop_bg).to_equal(defaults.desktop_bg)
expect(colors.accent).to_equal(defaults.accent)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/common/ui/wm_theme_css_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering WM theme CSS/HTML parser.
- WM theme CSS/HTML parser

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

- `REQ-SSPEC-UNIT`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `61531dc4eefe0587fb4281e166c87e895090542db483760eb2140b379ee2cabf`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `61531dc4eefe0587fb4281e166c87e895090542db483760eb2140b379ee2cabf`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `61531dc4eefe0587fb4281e166c87e895090542db483760eb2140b379ee2cabf`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/01_unit/lib/common/ui/wm_theme_css_spec.spl
mirror: doc/06_spec/01_unit/lib/common/ui/wm_theme_css_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/lib/common/ui/wm_theme_css_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/lib/common/ui/wm_theme_css_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/lib/common/ui/wm_theme_css_spec.spl:23:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'parses all 6 --wm-* custom properties from raw CSS' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/common/ui/wm_theme_css_spec.spl:43:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'disambiguates --wm-surface from the longer --wm-surface-hover' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/common/ui/wm_theme_css_spec.spl:51:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'extracts tokens from a <style> block inside an HTML document' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
