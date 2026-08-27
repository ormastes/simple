# Aqua Theme Contract

> Value-level contract for the classic Mac OS X "Aqua" light glass palette that

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 3 | 3 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Aqua Theme Contract

Value-level contract for the classic Mac OS X "Aqua" light glass palette that

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/03_system/gui/wm_aqua_theme_contract_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

Value-level contract for the classic Mac OS X "Aqua" light glass palette that
`wm_chrome_theme()` now returns by default (see wm_chrome_theme_spec.spl for
the byte-for-byte pixel-pipeline evidence; this spec pins the palette VALUES
and the accessibility property they encode: dark title/label text over the
light Aqua chrome, not saturated accent-on-text).

A contrast guard computes a simple relative luminance from each color's RGB
channels so a future palette edit that silently regresses dark-text-on-light-
chrome contrast fails this spec instead of shipping unnoticed. The
`aqua_light()` registry factory (glass/theme.spl) is spot-checked for
consistency with the wm_chrome accent, since both derive from the same named
Aqua palette (glass/numeric_tokens.spl AQUA_LIGHT_*).

## Scenarios

### Aqua chrome theme palette

#### wm_chrome_theme returns the Aqua palette values

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- wm_chrome_theme returns the Aqua palette values
   - Expected: theme.desktop_bg equals `0xff5a7fb5u32`
   - Expected: theme.window_body equals `0xfff2f2f2u32`
   - Expected: theme.title_focused equals `0xffdceafbu32`
   - Expected: theme.title_unfocused equals `0xffe2e2e6u32`
   - Expected: theme.accent equals `0xff2c6fefu32`
   - Expected: theme.text_primary equals `0xff1d1d1fu32`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("wm_chrome_theme returns the Aqua palette values")
reset_wm_chrome_theme()
val theme = wm_chrome_theme()
expect(theme.desktop_bg).to_equal(0xff5a7fb5u32)
expect(theme.window_body).to_equal(0xfff2f2f2u32)
expect(theme.title_focused).to_equal(0xffdceafbu32)
expect(theme.title_unfocused).to_equal(0xffe2e2e6u32)
expect(theme.accent).to_equal(0xff2c6fefu32)
expect(theme.text_primary).to_equal(0xff1d1d1fu32)
```

</details>

### Aqua chrome theme contrast guard

#### text_primary stays comfortably darker than the chrome it sits on

- text_primary stays comfortably darker than the chrome it sits on
- Read the default Aqua palette
- Compute relative luminance for text vs. the two chrome fills it is painted over
- Assert a comfortable dark-text-on-light-chrome contrast margin


<details>
<summary>Executable SSpec</summary>

Runnable source: 18 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("text_primary stays comfortably darker than the chrome it sits on")
step("Read the default Aqua palette")
val theme = wm_chrome_theme_defaults()

step("Compute relative luminance for text vs. the two chrome fills it is painted over")
val text_luminance = _relative_luminance_x1000(theme.text_primary)
val title_luminance = _relative_luminance_x1000(theme.title_focused)
val body_luminance = _relative_luminance_x1000(theme.window_body)

step("Assert a comfortable dark-text-on-light-chrome contrast margin")
# text_primary (~29,29,31) is near-black; title_focused (~220,234,251)
# and window_body (242,242,242) are both near-white. A future palette
# edit that darkens the chrome or lightens the text enough to erode
# readability trips this margin (100000 == luminance delta of 100 on
# the unscaled 0..255 channel range).
expect(title_luminance - text_luminance).to_be_greater_than(100000)
expect(body_luminance - text_luminance).to_be_greater_than(100000)
```

</details>

### Aqua registry theme factory consistency

#### aqua_light() UITheme accent matches the wm_chrome Aqua accent

- aqua_light() UITheme accent matches the wm_chrome Aqua accent
   - Expected: theme.name equals `aqua_light`
   - Expected: accent_argb equals `wm_chrome_theme_defaults().accent`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("aqua_light() UITheme accent matches the wm_chrome Aqua accent")
val theme = aqua_light()
expect(theme.name).to_equal("aqua_light")
val accent_argb = wm_css_color_to_argb(theme.colors.accent.to_css())
expect(accent_argb).to_equal(wm_chrome_theme_defaults().accent)
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

- Canonical SPipe generation for source `fcfba3ad03c9b1342c3cdd6d47f74147e7bbda7e51b47f640db0c273c4504773`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `fcfba3ad03c9b1342c3cdd6d47f74147e7bbda7e51b47f640db0c273c4504773`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `fcfba3ad03c9b1342c3cdd6d47f74147e7bbda7e51b47f640db0c273c4504773`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/03_system/gui/wm_aqua_theme_contract_spec.spl
mirror: doc/06_spec/03_system/gui/wm_aqua_theme_contract_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/03_system/gui/wm_aqua_theme_contract_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/gui/wm_aqua_theme_contract_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/gui/wm_aqua_theme_contract_spec.spl:48:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'wm_chrome_theme returns the Aqua palette values' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/gui/wm_aqua_theme_contract_spec.spl:62:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'text_primary stays comfortably darker than the chrome it sits on' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/gui/wm_aqua_theme_contract_spec.spl:84:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'aqua_light() UITheme accent matches the wm_chrome Aqua accent' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
