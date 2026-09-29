# Wm Chrome Theme Specification

> Tests covering WM chrome theme accessor, WM chrome theme drives the Draw IR projection, WM chrome shares the GUI (CSS) theme, WM chrome theme drives the desktop-resolution pixel fallback.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 11 | 11 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Wm Chrome Theme Specification

## Scenarios

### WM chrome theme accessor

#### defaults reproduce the Aqua-light chrome literals byte-for-byte

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- defaults reproduce the Aqua-light chrome literals byte-for-byte
   - Expected: d.desktop_bg equals `0xff5a7fb5u32`
   - Expected: d.compositor_bg equals `0xff5a7fb5u32`
   - Expected: d.command_lane equals `0xfff5f5f7u32`
   - Expected: d.taskbar equals `0xffe8e8ecu32`
   - Expected: d.text_primary equals `0xff1d1d1fu32`
   - Expected: d.title_focused equals `0xffdceafbu32`
   - Expected: d.title_unfocused equals `0xffe2e2e6u32`
   - Expected: d.window_shadow equals `0x28000000u32`
   - Expected: d.window_body equals `0xfff2f2f2u32`
   - Expected: d.host_window_body equals `0xffe8e8e8u32`
   - Expected: d.accent equals `0xff2c6fefu32`
   - Expected: d.close_button equals `0xffff5f57u32`
   - Expected: d.background_hex equals `#5A7FB5`


<details>
<summary>Executable SSpec</summary>

Runnable source: 17 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("defaults reproduce the Aqua-light chrome literals byte-for-byte")
reset_wm_chrome_theme()
val d = wm_chrome_theme_defaults()
expect(d.desktop_bg).to_equal(0xff5a7fb5u32)
expect(d.compositor_bg).to_equal(0xff5a7fb5u32)
expect(d.command_lane).to_equal(0xfff5f5f7u32)
expect(d.taskbar).to_equal(0xffe8e8ecu32)
expect(d.text_primary).to_equal(0xff1d1d1fu32)
expect(d.title_focused).to_equal(0xffdceafbu32)
expect(d.title_unfocused).to_equal(0xffe2e2e6u32)
expect(d.window_shadow).to_equal(0x28000000u32)
expect(d.window_body).to_equal(0xfff2f2f2u32)
expect(d.host_window_body).to_equal(0xffe8e8e8u32)
expect(d.accent).to_equal(0xff2c6fefu32)
expect(d.close_button).to_equal(0xffff5f57u32)
expect(d.background_hex).to_equal("#5A7FB5")
```

</details>

#### returns defaults when no theme is installed and honors a registered theme

- returns defaults when no theme is installed and honors a registered theme
   - Expected: wm_chrome_theme().desktop_bg equals `0xff5a7fb5u32`
   - Expected: wm_chrome_theme().desktop_bg equals `0xff010203u32`
   - Expected: wm_chrome_theme().accent equals `0xff1c1d1eu32`
   - Expected: wm_chrome_theme().desktop_bg equals `0xff5a7fb5u32`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("returns defaults when no theme is installed and honors a registered theme")
reset_wm_chrome_theme()
expect(wm_chrome_theme().desktop_bg).to_equal(0xff5a7fb5u32)
register_wm_chrome_theme(_custom_theme())
expect(wm_chrome_theme().desktop_bg).to_equal(0xff010203u32)
expect(wm_chrome_theme().accent).to_equal(0xff1c1d1eu32)
reset_wm_chrome_theme()
expect(wm_chrome_theme().desktop_bg).to_equal(0xff5a7fb5u32)
```

</details>

### WM chrome theme drives the Draw IR projection

#### chrome batch colors come from the accessor (default palette)

- chrome batch colors come from the accessor (default palette)
   - Expected: comp.batches[0].commands[0].color equals `theme.desktop_bg`
   - Expected: comp.batches[1].commands[0].color equals `theme.command_lane`
   - Expected: comp.batches[1].commands[1].color equals `theme.taskbar`
   - Expected: comp.batches[2].commands[1].color equals `theme.window_body`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("chrome batch colors come from the accessor (default palette)")
reset_wm_chrome_theme()
val theme = wm_chrome_theme()
val comp = shared_wm_scene_draw_ir_composition(_scene(), _taskbar(), DRAW_IR_BACKEND_GPU, 1000, "09:41", 1)
expect(comp.batches[0].commands[0].color).to_equal(theme.desktop_bg)
expect(comp.batches[1].commands[0].color).to_equal(theme.command_lane)
expect(comp.batches[1].commands[1].color).to_equal(theme.taskbar)
expect(comp.batches[2].commands[1].color).to_equal(theme.window_body)
```

</details>

#### installing a theme changes the projected chrome colors

- installing a theme changes the projected chrome colors
   - Expected: comp.batches[0].commands[0].color equals `0xff010203u32`
   - Expected: comp.batches[1].commands[0].color equals `0xff070809u32`
   - Expected: comp.batches[1].commands[1].color equals `0xff0a0b0cu32`
   - Expected: comp.batches[2].commands[1].color equals `0xff161718u32`
   - Expected: restored.batches[0].commands[0].color equals `0xff5a7fb5u32`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("installing a theme changes the projected chrome colors")
register_wm_chrome_theme(_custom_theme())
val comp = shared_wm_scene_draw_ir_composition(_scene(), _taskbar(), DRAW_IR_BACKEND_GPU, 1000, "09:41", 1)
expect(comp.batches[0].commands[0].color).to_equal(0xff010203u32)
expect(comp.batches[1].commands[0].color).to_equal(0xff070809u32)
expect(comp.batches[1].commands[1].color).to_equal(0xff0a0b0cu32)
expect(comp.batches[2].commands[1].color).to_equal(0xff161718u32)
reset_wm_chrome_theme()
val restored = shared_wm_scene_draw_ir_composition(_scene(), _taskbar(), DRAW_IR_BACKEND_GPU, 1000, "09:41", 1)
expect(restored.batches[0].commands[0].color).to_equal(0xff5a7fb5u32)
```

</details>

### WM chrome shares the GUI (CSS) theme

#### parses css hex rgb and rgba colors into ARGB (0 sentinel otherwise)

- parses css hex rgb and rgba colors into ARGB (0 sentinel otherwise)
   - Expected: wm_css_color_to_argb("#0f172a") equals `0xff0f172au32`
   - Expected: wm_css_color_to_argb("#FFF") equals `0xffffffffu32`
   - Expected: wm_css_color_to_argb(" #2563eb ") equals `0xff2563ebu32`
   - Expected: wm_css_color_to_argb("#1f1f21cc") equals `0xcc1f1f21u32`
   - Expected: wm_css_color_to_argb("#abcd") equals `0xddaabbccu32`
   - Expected: wm_css_color_to_argb("rgb(31, 32, 33)") equals `0xff1f2021u32`
   - Expected: wm_css_color_to_argb("rgba(31,31,33,0.80)") equals `0xcc1f1f21u32`
   - Expected: wm_css_color_to_argb("rgba(53,52,55,0.75)") equals `0xbf353437u32`
   - Expected: wm_css_color_to_argb("") equals `0u32`
   - Expected: wm_css_color_to_argb("not-a-color") equals `0u32`
   - Expected: wm_css_color_to_argb("#12") equals `0u32`
   - Expected: wm_css_color_to_argb("rgba(1,2,3,1.5)") equals `0u32`


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("parses css hex rgb and rgba colors into ARGB (0 sentinel otherwise)")
expect(wm_css_color_to_argb("#0f172a")).to_equal(0xff0f172au32)
expect(wm_css_color_to_argb("#FFF")).to_equal(0xffffffffu32)
expect(wm_css_color_to_argb(" #2563eb ")).to_equal(0xff2563ebu32)
expect(wm_css_color_to_argb("#1f1f21cc")).to_equal(0xcc1f1f21u32)
expect(wm_css_color_to_argb("#abcd")).to_equal(0xddaabbccu32)
expect(wm_css_color_to_argb("rgb(31, 32, 33)")).to_equal(0xff1f2021u32)
expect(wm_css_color_to_argb("rgba(31,31,33,0.80)")).to_equal(0xcc1f1f21u32)
expect(wm_css_color_to_argb("rgba(53,52,55,0.75)")).to_equal(0xbf353437u32)
expect(wm_css_color_to_argb("")).to_equal(0u32)
expect(wm_css_color_to_argb("not-a-color")).to_equal(0u32)
expect(wm_css_color_to_argb("#12")).to_equal(0u32)
expect(wm_css_color_to_argb("rgba(1,2,3,1.5)")).to_equal(0u32)
```

</details>

#### maps GUI tokens onto the chrome palette with per-field default fallback

- maps GUI tokens onto the chrome palette with per-field default fallback
   - Expected: mapped.compositor_bg equals `0xff111213u32`
   - Expected: mapped.desktop_bg equals `0xff111213u32`
   - Expected: mapped.text_primary equals `0xffe2e8f0u32`
   - Expected: mapped.title_focused equals `0xff007affu32`
   - Expected: mapped.accent equals `0xff007affu32`
   - Expected: mapped.window_body equals `0xff1f2937u32`
   - Expected: mapped.host_window_body equals `0xff1f2937u32`
   - Expected: mapped.taskbar equals `0xff1f2937u32`
   - Expected: mapped.title_unfocused equals `0xff374151u32`
   - Expected: mapped.close_button equals `0xffff3b30u32`
   - Expected: mapped.background_hex equals `#111213`
   - Expected: partial.compositor_bg equals `0xff5a7fb5u32`
   - Expected: partial.text_primary equals `0xff1d1d1fu32`
   - Expected: partial.accent equals `0xff007affu32`
   - Expected: partial.close_button equals `0xffff5f57u32`
   - Expected: partial.background_hex equals `#5A7FB5`


<details>
<summary>Executable SSpec</summary>

Runnable source: 21 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("maps GUI tokens onto the chrome palette with per-field default fallback")
val mapped = wm_chrome_colors_from_gui_tokens("#111213", "#e2e8f0", "#007AFF", "#1f2937", "#374151", "#FF3B30")
expect(mapped.compositor_bg).to_equal(0xff111213u32)
expect(mapped.desktop_bg).to_equal(0xff111213u32)
expect(mapped.text_primary).to_equal(0xffe2e8f0u32)
expect(mapped.title_focused).to_equal(0xff007affu32)
expect(mapped.accent).to_equal(0xff007affu32)
expect(mapped.window_body).to_equal(0xff1f2937u32)
expect(mapped.host_window_body).to_equal(0xff1f2937u32)
expect(mapped.taskbar).to_equal(0xff1f2937u32)
expect(mapped.title_unfocused).to_equal(0xff374151u32)
expect(mapped.close_button).to_equal(0xffff3b30u32)
expect(mapped.background_hex).to_equal("#111213")
# missing/unparseable tokens keep the byte-identical defaults
val partial = wm_chrome_colors_from_gui_tokens("", "bad", "#007AFF", "", "", "")
expect(partial.compositor_bg).to_equal(0xff5a7fb5u32)
expect(partial.text_primary).to_equal(0xff1d1d1fu32)
expect(partial.accent).to_equal(0xff007affu32)
expect(partial.close_button).to_equal(0xffff5f57u32)
expect(partial.background_hex).to_equal("#5A7FB5")
```

</details>

#### preserves Aetheric translucent surfaces instead of falling back to Aqua

- preserves Aetheric translucent surfaces instead of falling back to Aqua
   - Expected: mapped.window_body equals `0xcc1f1f21u32`
   - Expected: mapped.host_window_body equals `0xcc1f1f21u32`
   - Expected: mapped.taskbar equals `0xcc1f1f21u32`
   - Expected: mapped.title_unfocused equals `0xcc353437u32`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("preserves Aetheric translucent surfaces instead of falling back to Aqua")
val mapped = wm_chrome_colors_from_gui_tokens("#0e0e10", "#e4e2e4", "#adc6ff", "rgba(31,31,33,0.80)", "rgba(53,52,55,0.80)", "#ffb4ab")
expect(mapped.window_body).to_equal(0xcc1f1f21u32)
expect(mapped.host_window_body).to_equal(0xcc1f1f21u32)
expect(mapped.taskbar).to_equal(0xcc1f1f21u32)
expect(mapped.title_unfocused).to_equal(0xcc353437u32)
expect(mapped.window_body == wm_chrome_theme_defaults().window_body).to_be(false)
```

</details>

#### a SimpleTheme's css tokens flow into the WM chrome in one call

- a SimpleTheme's css tokens flow into the WM chrome in one call
   - Expected: derived.compositor_bg equals `0xff101112u32`
   - Expected: derived.text_primary equals `0xfff0f1f2u32`
   - Expected: derived.accent equals `0xff22c55eu32`
   - Expected: derived.window_body equals `0xff1a1b1cu32`
   - Expected: derived.title_unfocused equals `0xff2a2b2cu32`
   - Expected: derived.close_button equals `0xffef4444u32`
   - Expected: wm_chrome_theme().compositor_bg equals `0xff101112u32`
   - Expected: wm_chrome_theme().accent equals `0xff22c55eu32`
   - Expected: wm_chrome_theme().compositor_bg equals `0xff5a7fb5u32`


<details>
<summary>Executable SSpec</summary>

Runnable source: 20 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("a SimpleTheme's css tokens flow into the WM chrome in one call")
reset_wm_chrome_theme()
# No :root braces: SimpleTheme's token parser is line-based (lines
# starting with --), and brace-bearing string literals risk the
# interpolation footgun.
val css = "--ui-bg: #101112;\n--ui-fg: #f0f1f2;\n--ui-accent: #22c55e;\n--app-surface: #1a1b1c;\n--app-surface-hover: #2a2b2c;\n--ui-error: #ef4444;"
val theme = SimpleTheme.from_css("spec-shared", css)
val derived = wm_chrome_colors_from_simple_theme(theme)
expect(derived.compositor_bg).to_equal(0xff101112u32)
expect(derived.text_primary).to_equal(0xfff0f1f2u32)
expect(derived.accent).to_equal(0xff22c55eu32)
expect(derived.window_body).to_equal(0xff1a1b1cu32)
expect(derived.title_unfocused).to_equal(0xff2a2b2cu32)
expect(derived.close_button).to_equal(0xffef4444u32)
apply_simple_theme_to_wm_chrome(theme)
expect(wm_chrome_theme().compositor_bg).to_equal(0xff101112u32)
expect(wm_chrome_theme().accent).to_equal(0xff22c55eu32)
reset_wm_chrome_theme()
expect(wm_chrome_theme().compositor_bg).to_equal(0xff5a7fb5u32)
```

</details>

#### applied GUI theme drives the projected Draw IR chrome and resets clean

- applied GUI theme drives the projected Draw IR chrome and resets clean
   - Expected: comp.batches[0].commands[0].color equals `0xff101112u32`
   - Expected: comp.batches[2].commands[1].color equals `0xff1a1b1cu32`
   - Expected: restored.batches[0].commands[0].color equals `0xff5a7fb5u32`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("applied GUI theme drives the projected Draw IR chrome and resets clean")
val css = "--ui-bg: #101112;\n--app-surface: #1a1b1c;"
apply_simple_theme_to_wm_chrome(SimpleTheme.from_css("spec-shared-ir", css))
val comp = shared_wm_scene_draw_ir_composition(_scene(), _taskbar(), DRAW_IR_BACKEND_GPU, 1000, "09:41", 1)
expect(comp.batches[0].commands[0].color).to_equal(0xff101112u32)
expect(comp.batches[2].commands[1].color).to_equal(0xff1a1b1cu32)
reset_wm_chrome_theme()
val restored = shared_wm_scene_draw_ir_composition(_scene(), _taskbar(), DRAW_IR_BACKEND_GPU, 1000, "09:41", 1)
expect(restored.batches[0].commands[0].color).to_equal(0xff5a7fb5u32)
```

</details>

### WM chrome theme drives the desktop-resolution pixel fallback

#### paints the themed desktop background through the direct fallback

- paints the themed desktop background through the direct fallback
   - Expected: pixels.len().to_i32() equals `1024 * 768`
   - Expected: pixels[5 * 1024 + 5] equals `0xff5a7fb5u32`
   - Expected: pixels[50 * 1024 + 100] equals `0xFF334155u32`


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("paints the themed desktop background through the direct fallback")
reset_wm_chrome_theme()
val scene = standard_wm_scene(1024, 768)
val pixels = wm_scene_direct_rect_pixels(scene)
expect(pixels.len().to_i32()).to_equal(1024 * 768)
# desktop backdrop pixel = desktop_chrome element color (standard_wm_scene
# now threads wm_chrome_theme().compositor_bg instead of a dark-slate
# literal, per this file's Aqua migration below)
expect(pixels[5 * 1024 + 5]).to_equal(0xff5a7fb5u32)
# decoration bar element (y 42..76) is a real rect, not near-blank
expect(pixels[50 * 1024 + 100]).to_equal(0xFF334155u32)
```

</details>

#### themed compositor background is the fallback base fill

- themed compositor background is the fallback base fill
   - Expected: base_default[767 * 1024 + 1023] equals `0xff5a7fb5u32`
   - Expected: base_themed[767 * 1024 + 1023] equals `0xff040506u32`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("themed compositor background is the fallback base fill")
reset_wm_chrome_theme()
val empty = WmSceneSpec(name: "empty", width: 1024, height: 768, elements: [])
val base_default = wm_scene_direct_rect_pixels(empty)
expect(base_default[767 * 1024 + 1023]).to_equal(0xff5a7fb5u32)
register_wm_chrome_theme(_custom_theme())
val base_themed = wm_scene_direct_rect_pixels(empty)
expect(base_themed[767 * 1024 + 1023]).to_equal(0xff040506u32)
reset_wm_chrome_theme()
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/03_system/gui/wm_compare/wm_chrome_theme_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering WM chrome theme accessor, WM chrome theme drives the Draw IR projection, WM chrome shares the GUI (CSS) theme, WM chrome theme drives the desktop-resolution pixel fallback.
- WM chrome theme accessor
- WM chrome theme drives the Draw IR projection
- WM chrome shares the GUI (CSS) theme
- WM chrome theme drives the desktop-resolution pixel fallback

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 11 |
| Active scenarios | 11 |
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

- Canonical SPipe generation for source `3d0bd9f4d462fb91995847feba460bfe88a25d6a65e1ba9349ee51bdea602a94`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `3d0bd9f4d462fb91995847feba460bfe88a25d6a65e1ba9349ee51bdea602a94`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `3d0bd9f4d462fb91995847feba460bfe88a25d6a65e1ba9349ee51bdea602a94`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/03_system/gui/wm_compare/wm_chrome_theme_spec.spl
mirror: doc/06_spec/03_system/gui/wm_compare/wm_chrome_theme_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/03_system/gui/wm_compare/wm_chrome_theme_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/gui/wm_compare/wm_chrome_theme_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/gui/wm_compare/wm_chrome_theme_spec.spl:72:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'defaults reproduce the Aqua-light chrome literals byte-for-byte' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/gui/wm_compare/wm_chrome_theme_spec.spl:91:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'returns defaults when no theme is installed and honors a registered theme' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/gui/wm_compare/wm_chrome_theme_spec.spl:104:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'chrome batch colors come from the accessor (default palette)' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
