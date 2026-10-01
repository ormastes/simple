# Wm Theme Css Wiring Specification

> Tests covering WM CSS theme host-side wiring (lane F2).

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 7 | 7 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Wm Theme Css Wiring Specification

## Scenarios

### WM CSS theme host-side wiring (lane F2)

#### installs a full known palette from CSS text and wm_chrome_theme() reflects it

- installs a full known palette from CSS text and wm_chrome_theme() reflects it
   - Expected: theme.desktop_bg equals `0xFF112233u32`
   - Expected: theme.text_primary equals `0xFF445566u32`
   - Expected: theme.title_focused equals `0xFF778899u32`
   - Expected: theme.command_lane equals `0xFFAABBCCu32`
   - Expected: theme.title_unfocused equals `0xFFDDEEFFu32`
   - Expected: theme.close_button equals `0xFFFF0000u32`


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("installs a full known palette from CSS text and wm_chrome_theme() reflects it")
reset_wm_chrome_theme()
val css = "--wm-bg: #112233; --wm-fg: #445566; --wm-accent: #778899; --wm-surface: #aabbcc; --wm-surface-hover: #ddeeff; --wm-error: #ff0000;"
val installed = apply_wm_css_theme_text(css)
expect(installed).to_be(true)
val theme = wm_chrome_theme()
expect(theme.desktop_bg).to_equal(0xFF112233u32)
expect(theme.text_primary).to_equal(0xFF445566u32)
expect(theme.title_focused).to_equal(0xFF778899u32)
expect(theme.command_lane).to_equal(0xFFAABBCCu32)
expect(theme.title_unfocused).to_equal(0xFFDDEEFFu32)
expect(theme.close_button).to_equal(0xFFFF0000u32)
reset_wm_chrome_theme()
```

</details>

#### installs from a <style> block inside HTML text too

- installs from a <style> block inside HTML text too
   - Expected: theme.desktop_bg equals `0xFF123456u32`
   - Expected: theme.title_focused equals `0xFFABCDEFu32`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("installs from a <style> block inside HTML text too")
reset_wm_chrome_theme()
val html = "<html><head><style>\n  --wm-bg: #123456;\n  --wm-accent: #abcdef;\n</style></head><body></body></html>"
val installed = apply_wm_css_theme_text(html)
expect(installed).to_be(true)
val theme = wm_chrome_theme()
expect(theme.desktop_bg).to_equal(0xFF123456u32)
expect(theme.title_focused).to_equal(0xFFABCDEFu32)
reset_wm_chrome_theme()
```

</details>

#### leaves byte-identical defaults untouched when CSS text is empty

- leaves byte-identical defaults untouched when CSS text is empty
   - Expected: theme.desktop_bg equals `defaults.desktop_bg`
   - Expected: theme.close_button equals `defaults.close_button`
   - Expected: theme.background_hex equals `defaults.background_hex`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("leaves byte-identical defaults untouched when CSS text is empty")
reset_wm_chrome_theme()
val defaults = wm_chrome_theme_defaults()
val installed = apply_wm_css_theme_text("")
expect(installed).to_be(false)
val theme = wm_chrome_theme()
expect(theme.desktop_bg).to_equal(defaults.desktop_bg)
expect(theme.close_button).to_equal(defaults.close_button)
expect(theme.background_hex).to_equal(defaults.background_hex)
```

</details>

#### leaves byte-identical defaults untouched when CSS text is garbage

- leaves byte-identical defaults untouched when CSS text is garbage
   - Expected: theme.desktop_bg equals `defaults.desktop_bg`
   - Expected: theme.accent equals `defaults.accent`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("leaves byte-identical defaults untouched when CSS text is garbage")
reset_wm_chrome_theme()
val defaults = wm_chrome_theme_defaults()
val installed = apply_wm_css_theme_text("this is not a stylesheet at all { nonsense: yes }")
expect(installed).to_be(false)
val theme = wm_chrome_theme()
expect(theme.desktop_bg).to_equal(defaults.desktop_bg)
expect(theme.accent).to_equal(defaults.accent)
```

</details>

#### never clobbers an already-installed theme (e.g. a generated snapshot) with garbage CSS

- never clobbers an already-installed theme (e.g. a generated snapshot) with garbage CSS
   - Expected: theme.desktop_bg equals `custom.desktop_bg`
   - Expected: theme.close_button equals `custom.close_button`


<details>
<summary>Executable SSpec</summary>

Runnable source: 25 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("never clobbers an already-installed theme (e.g. a generated snapshot) with garbage CSS")
reset_wm_chrome_theme()
val custom = WmChromeColors(
    desktop_bg: 0xFFAA1122u32,
    compositor_bg: 0xFFAA1122u32,
    command_lane: 0xFFAA1133u32,
    taskbar: 0xFFAA1144u32,
    text_primary: 0xFFAA1155u32,
    title_focused: 0xFFAA1166u32,
    title_unfocused: 0xFFAA1177u32,
    window_shadow: 0x28000000u32,
    window_body: 0xFFAA1188u32,
    host_window_body: 0xFFAA1199u32,
    accent: 0xFFAA11AAu32,
    close_button: 0xFFAA11BBu32,
    background_hex: "#AA1122"
)
register_wm_chrome_theme(custom)
val installed = apply_wm_css_theme_text("garbage, no tokens here")
expect(installed).to_be(false)
val theme = wm_chrome_theme()
expect(theme.desktop_bg).to_equal(custom.desktop_bg)
expect(theme.close_button).to_equal(custom.close_button)
reset_wm_chrome_theme()
```

</details>

#### the guest-side call point (simpleos_wm_theme_bootstrap) delegates to the same wiring

- the guest-side call point (simpleos_wm_theme_bootstrap) delegates to the same wiring
   - Expected: theme.desktop_bg equals `0xFF0F172Au32`
   - Expected: theme.title_focused equals `0xFF2050A0u32`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("the guest-side call point (simpleos_wm_theme_bootstrap) delegates to the same wiring")
reset_wm_chrome_theme()
val css = "--wm-bg: #0f172a; --wm-fg: #f8fafc; --wm-accent: #2050a0; --wm-surface: #1e293b; --wm-surface-hover: #334155; --wm-error: #dc2626;"
val installed = apply_simpleos_css_theme_override(css)
expect(installed).to_be(true)
val theme = wm_chrome_theme()
expect(theme.desktop_bg).to_equal(0xFF0F172Au32)
expect(theme.title_focused).to_equal(0xFF2050A0u32)
reset_wm_chrome_theme()
```

</details>

#### the guest-side call point is also garbage-safe

- the guest-side call point is also garbage-safe
   - Expected: wm_chrome_theme().desktop_bg equals `defaults.desktop_bg`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("the guest-side call point is also garbage-safe")
reset_wm_chrome_theme()
val defaults = wm_chrome_theme_defaults()
val installed = apply_simpleos_css_theme_override("")
expect(installed).to_be(false)
expect(wm_chrome_theme().desktop_bg).to_equal(defaults.desktop_bg)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/common/ui/wm_theme_css_wiring_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering WM CSS theme host-side wiring (lane F2).
- WM CSS theme host-side wiring (lane F2)

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

- Canonical SPipe generation for source `e161f35c847f1bdea0da2fdf18f120157a2139efcf95b2b7311fa0ba0ba53dab`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `e161f35c847f1bdea0da2fdf18f120157a2139efcf95b2b7311fa0ba0ba53dab`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `e161f35c847f1bdea0da2fdf18f120157a2139efcf95b2b7311fa0ba0ba53dab`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/01_unit/lib/common/ui/wm_theme_css_wiring_spec.spl
mirror: doc/06_spec/01_unit/lib/common/ui/wm_theme_css_wiring_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/lib/common/ui/wm_theme_css_wiring_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/lib/common/ui/wm_theme_css_wiring_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/lib/common/ui/wm_theme_css_wiring_spec.spl:28:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'installs a full known palette from CSS text and wm_chrome_theme() reflects it' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/common/ui/wm_theme_css_wiring_spec.spl:44:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'installs from a <style> block inside HTML text too' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/common/ui/wm_theme_css_wiring_spec.spl:56:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'leaves byte-identical defaults untouched when CSS text is empty' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
