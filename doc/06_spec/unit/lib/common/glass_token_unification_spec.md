# Glass Token Unification Specification

> AC-1: GUI lib and window manager consume the same theme tokens -- a single theme change propagates to both.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 30 | 30 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Glass Token Unification Specification

AC-1: GUI lib and window manager consume the same theme tokens -- a single theme change propagates to both.

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #GUI-THEME-SHARING |
| Category | Infrastructure |
| Difficulty | 2/5 |
| Status | Draft |
| Requirements | N/A |
| Plan | N/A |
| Design | doc/05_design/stitch_design_system.md |
| Source | `test/unit/lib/common/glass_token_unification_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

AC-1: GUI lib and window manager consume the same theme tokens -- a single
theme change propagates to both.

AC-7: Bugs in existing GUI/WM/theme code identified and fixed. The primary
bug is that glass_effects.spl hardcodes values instead of importing from
glass_numeric_tokens.spl.

After the fix, GlassConfig factory methods in glass_effects.spl must import
from glass_numeric_tokens.spl constants, so both the compositor (baremetal
u64 values) and the GUI widget lib (CSS rgba strings in glass_tokens.spl)
derive from the same single source of truth.

## Key Concepts

| Concept | Description |
|---------|-------------|
| GlassConfig | Compositor-level struct with u64 color/blur/shadow fields |
| GlassColorTokens | CSS-text token struct for the widget system |
| glass_numeric_tokens | Canonical u64 hex constants (single source of truth) |

## Behavior

- GlassConfig.dark().surface_color must equal GLASS_DARK_SURFACE
- GlassConfig.dark().surface_alpha must equal GLASS_DARK_SURFACE_A
- GlassConfig.dark().border_color must equal GLASS_DARK_BORDER
- GlassConfig.dark().border_alpha must equal GLASS_DARK_BORDER_A
- GlassConfig.dark().accent_color must equal GLASS_DARK_ACCENT
- GlassConfig.dark().blur_radius must equal GLASS_BLUR_SURFACE
- GlassConfig.dark().shadow_blur must equal GLASS_SHADOW_BLUR
- GlassConfig.dark().shadow_offset must equal GLASS_SHADOW_OFFSET
- GlassConfig.light().surface_color must equal GLASS_LIGHT_SURFACE
- GlassConfig.light().border_alpha must equal GLASS_LIGHT_BORDER_A
- GlassConfig.obsidian_dark().surface_color must equal GLASS_OBSIDIAN_SURFACE
- GlassConfig.obsidian_dark().accent_color must equal GLASS_OBSIDIAN_ACCENT

## Scenarios

### GlassConfig.dark() token unification

#### surface_color matches GLASS_DARK_SURFACE

- surface_color matches GLASS_DARK_SURFACE
   - Expected: config.surface_color equals `GLASS_DARK_SURFACE.to_u32()`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("surface_color matches GLASS_DARK_SURFACE")
val config = GlassConfig.dark()
expect(config.surface_color).to_equal(GLASS_DARK_SURFACE.to_u32())
```

</details>

#### surface_alpha matches GLASS_DARK_SURFACE_A

- surface_alpha matches GLASS_DARK_SURFACE_A
   - Expected: config.surface_alpha equals `GLASS_DARK_SURFACE_A.to_u8()`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("surface_alpha matches GLASS_DARK_SURFACE_A")
val config = GlassConfig.dark()
expect(config.surface_alpha).to_equal(GLASS_DARK_SURFACE_A.to_u8())
```

</details>

#### blur_radius matches GLASS_BLUR_SURFACE

- blur_radius matches GLASS_BLUR_SURFACE
   - Expected: config.blur_radius equals `GLASS_BLUR_SURFACE.to_u32()`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("blur_radius matches GLASS_BLUR_SURFACE")
val config = GlassConfig.dark()
expect(config.blur_radius).to_equal(GLASS_BLUR_SURFACE.to_u32())
```

</details>

#### border_color matches GLASS_DARK_BORDER

- border_color matches GLASS_DARK_BORDER
   - Expected: config.border_color equals `GLASS_DARK_BORDER.to_u32()`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("border_color matches GLASS_DARK_BORDER")
val config = GlassConfig.dark()
expect(config.border_color).to_equal(GLASS_DARK_BORDER.to_u32())
```

</details>

#### border_alpha matches GLASS_DARK_BORDER_A

- border_alpha matches GLASS_DARK_BORDER_A
   - Expected: config.border_alpha equals `GLASS_DARK_BORDER_A.to_u8()`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("border_alpha matches GLASS_DARK_BORDER_A")
val config = GlassConfig.dark()
expect(config.border_alpha).to_equal(GLASS_DARK_BORDER_A.to_u8())
```

</details>

#### shadow_offset matches GLASS_SHADOW_OFFSET

- shadow_offset matches GLASS_SHADOW_OFFSET
   - Expected: config.shadow_offset equals `GLASS_SHADOW_OFFSET.to_i32()`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("shadow_offset matches GLASS_SHADOW_OFFSET")
val config = GlassConfig.dark()
expect(config.shadow_offset).to_equal(GLASS_SHADOW_OFFSET.to_i32())
```

</details>

#### shadow_blur matches GLASS_SHADOW_BLUR

- shadow_blur matches GLASS_SHADOW_BLUR
   - Expected: config.shadow_blur equals `GLASS_SHADOW_BLUR.to_u32()`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("shadow_blur matches GLASS_SHADOW_BLUR")
val config = GlassConfig.dark()
expect(config.shadow_blur).to_equal(GLASS_SHADOW_BLUR.to_u32())
```

</details>

#### shadow_alpha matches GLASS_DARK_SHADOW_A

- shadow_alpha matches GLASS_DARK_SHADOW_A
   - Expected: config.shadow_alpha equals `GLASS_DARK_SHADOW_A.to_u8()`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("shadow_alpha matches GLASS_DARK_SHADOW_A")
val config = GlassConfig.dark()
expect(config.shadow_alpha).to_equal(GLASS_DARK_SHADOW_A.to_u8())
```

</details>

#### accent_color matches GLASS_DARK_ACCENT

- accent_color matches GLASS_DARK_ACCENT
   - Expected: config.accent_color equals `GLASS_DARK_ACCENT.to_u32()`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("accent_color matches GLASS_DARK_ACCENT")
val config = GlassConfig.dark()
expect(config.accent_color).to_equal(GLASS_DARK_ACCENT.to_u32())
```

</details>

#### accent2_color matches GLASS_DARK_ACCENT2

- accent2_color matches GLASS_DARK_ACCENT2
   - Expected: config.accent2_color equals `GLASS_DARK_ACCENT2.to_u32()`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("accent2_color matches GLASS_DARK_ACCENT2")
val config = GlassConfig.dark()
expect(config.accent2_color).to_equal(GLASS_DARK_ACCENT2.to_u32())
```

</details>

#### bg_top matches GLASS_DARK_BG_TOP

- bg_top matches GLASS_DARK_BG_TOP
   - Expected: config.bg_top equals `GLASS_DARK_BG_TOP.to_u32()`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("bg_top matches GLASS_DARK_BG_TOP")
val config = GlassConfig.dark()
expect(config.bg_top).to_equal(GLASS_DARK_BG_TOP.to_u32())
```

</details>

#### bg_bottom matches GLASS_DARK_BG_BOT

- bg_bottom matches GLASS_DARK_BG_BOT
   - Expected: config.bg_bottom equals `GLASS_DARK_BG_BOT.to_u32()`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("bg_bottom matches GLASS_DARK_BG_BOT")
val config = GlassConfig.dark()
expect(config.bg_bottom).to_equal(GLASS_DARK_BG_BOT.to_u32())
```

</details>

### GlassConfig.light() token unification

#### surface_color matches GLASS_LIGHT_SURFACE

- surface_color matches GLASS_LIGHT_SURFACE
   - Expected: config.surface_color equals `GLASS_LIGHT_SURFACE.to_u32()`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("surface_color matches GLASS_LIGHT_SURFACE")
val config = GlassConfig.light()
expect(config.surface_color).to_equal(GLASS_LIGHT_SURFACE.to_u32())
```

</details>

#### surface_alpha matches GLASS_LIGHT_SURFACE_A

- surface_alpha matches GLASS_LIGHT_SURFACE_A
   - Expected: config.surface_alpha equals `GLASS_LIGHT_SURFACE_A.to_u8()`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("surface_alpha matches GLASS_LIGHT_SURFACE_A")
val config = GlassConfig.light()
expect(config.surface_alpha).to_equal(GLASS_LIGHT_SURFACE_A.to_u8())
```

</details>

#### border_color matches GLASS_LIGHT_BORDER

- border_color matches GLASS_LIGHT_BORDER
   - Expected: config.border_color equals `GLASS_LIGHT_BORDER.to_u32()`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("border_color matches GLASS_LIGHT_BORDER")
val config = GlassConfig.light()
expect(config.border_color).to_equal(GLASS_LIGHT_BORDER.to_u32())
```

</details>

#### border_alpha matches GLASS_LIGHT_BORDER_A

- border_alpha matches GLASS_LIGHT_BORDER_A
   - Expected: config.border_alpha equals `GLASS_LIGHT_BORDER_A.to_u8()`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("border_alpha matches GLASS_LIGHT_BORDER_A")
val config = GlassConfig.light()
expect(config.border_alpha).to_equal(GLASS_LIGHT_BORDER_A.to_u8())
```

</details>

#### accent_color matches GLASS_LIGHT_ACCENT

- accent_color matches GLASS_LIGHT_ACCENT
   - Expected: config.accent_color equals `GLASS_LIGHT_ACCENT.to_u32()`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("accent_color matches GLASS_LIGHT_ACCENT")
val config = GlassConfig.light()
expect(config.accent_color).to_equal(GLASS_LIGHT_ACCENT.to_u32())
```

</details>

#### accent2_color matches GLASS_LIGHT_ACCENT2

- accent2_color matches GLASS_LIGHT_ACCENT2
   - Expected: config.accent2_color equals `GLASS_LIGHT_ACCENT2.to_u32()`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("accent2_color matches GLASS_LIGHT_ACCENT2")
val config = GlassConfig.light()
expect(config.accent2_color).to_equal(GLASS_LIGHT_ACCENT2.to_u32())
```

</details>

#### bg_top matches GLASS_LIGHT_BG_TOP

- bg_top matches GLASS_LIGHT_BG_TOP
   - Expected: config.bg_top equals `GLASS_LIGHT_BG_TOP.to_u32()`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("bg_top matches GLASS_LIGHT_BG_TOP")
val config = GlassConfig.light()
expect(config.bg_top).to_equal(GLASS_LIGHT_BG_TOP.to_u32())
```

</details>

#### bg_bottom matches GLASS_LIGHT_BG_BOT

- bg_bottom matches GLASS_LIGHT_BG_BOT
   - Expected: config.bg_bottom equals `GLASS_LIGHT_BG_BOT.to_u32()`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("bg_bottom matches GLASS_LIGHT_BG_BOT")
val config = GlassConfig.light()
expect(config.bg_bottom).to_equal(GLASS_LIGHT_BG_BOT.to_u32())
```

</details>

### GlassConfig.obsidian_dark() token unification

#### surface_color matches GLASS_OBSIDIAN_SURFACE

- surface_color matches GLASS_OBSIDIAN_SURFACE
   - Expected: config.surface_color equals `GLASS_OBSIDIAN_SURFACE.to_u32()`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("surface_color matches GLASS_OBSIDIAN_SURFACE")
val config = GlassConfig.obsidian_dark()
expect(config.surface_color).to_equal(GLASS_OBSIDIAN_SURFACE.to_u32())
```

</details>

#### surface_alpha matches GLASS_OBSIDIAN_SURFACE_A

- surface_alpha matches GLASS_OBSIDIAN_SURFACE_A
   - Expected: config.surface_alpha equals `GLASS_OBSIDIAN_SURFACE_A.to_u8()`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("surface_alpha matches GLASS_OBSIDIAN_SURFACE_A")
val config = GlassConfig.obsidian_dark()
expect(config.surface_alpha).to_equal(GLASS_OBSIDIAN_SURFACE_A.to_u8())
```

</details>

#### border_color matches GLASS_OBSIDIAN_BORDER

- border_color matches GLASS_OBSIDIAN_BORDER
   - Expected: config.border_color equals `GLASS_OBSIDIAN_BORDER.to_u32()`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("border_color matches GLASS_OBSIDIAN_BORDER")
val config = GlassConfig.obsidian_dark()
expect(config.border_color).to_equal(GLASS_OBSIDIAN_BORDER.to_u32())
```

</details>

#### border_alpha matches GLASS_OBSIDIAN_BORDER_A

- border_alpha matches GLASS_OBSIDIAN_BORDER_A
   - Expected: config.border_alpha equals `GLASS_OBSIDIAN_BORDER_A.to_u8()`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("border_alpha matches GLASS_OBSIDIAN_BORDER_A")
val config = GlassConfig.obsidian_dark()
expect(config.border_alpha).to_equal(GLASS_OBSIDIAN_BORDER_A.to_u8())
```

</details>

#### accent_color matches GLASS_OBSIDIAN_ACCENT

- accent_color matches GLASS_OBSIDIAN_ACCENT
   - Expected: config.accent_color equals `GLASS_OBSIDIAN_ACCENT.to_u32()`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("accent_color matches GLASS_OBSIDIAN_ACCENT")
val config = GlassConfig.obsidian_dark()
expect(config.accent_color).to_equal(GLASS_OBSIDIAN_ACCENT.to_u32())
```

</details>

#### bg_top matches GLASS_OBSIDIAN_BG_TOP

- bg_top matches GLASS_OBSIDIAN_BG_TOP
   - Expected: config.bg_top equals `GLASS_OBSIDIAN_BG_TOP.to_u32()`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("bg_top matches GLASS_OBSIDIAN_BG_TOP")
val config = GlassConfig.obsidian_dark()
expect(config.bg_top).to_equal(GLASS_OBSIDIAN_BG_TOP.to_u32())
```

</details>

#### bg_bottom matches GLASS_OBSIDIAN_BG_BOT

- bg_bottom matches GLASS_OBSIDIAN_BG_BOT
   - Expected: config.bg_bottom equals `GLASS_OBSIDIAN_BG_BOT.to_u32()`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("bg_bottom matches GLASS_OBSIDIAN_BG_BOT")
val config = GlassConfig.obsidian_dark()
expect(config.bg_bottom).to_equal(GLASS_OBSIDIAN_BG_BOT.to_u32())
```

</details>

### Shared constants across themes

#### all themes share the same blur_radius

- all themes share the same blur_radius
   - Expected: dark.blur_radius equals `GLASS_BLUR_SURFACE.to_u32()`
   - Expected: light.blur_radius equals `GLASS_BLUR_SURFACE.to_u32()`
   - Expected: obsidian.blur_radius equals `GLASS_BLUR_SURFACE.to_u32()`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("all themes share the same blur_radius")
val dark = GlassConfig.dark()
val light = GlassConfig.light()
val obsidian = GlassConfig.obsidian_dark()
expect(dark.blur_radius).to_equal(GLASS_BLUR_SURFACE.to_u32())
expect(light.blur_radius).to_equal(GLASS_BLUR_SURFACE.to_u32())
expect(obsidian.blur_radius).to_equal(GLASS_BLUR_SURFACE.to_u32())
```

</details>

#### all themes share the same shadow_blur

- all themes share the same shadow_blur
   - Expected: dark.shadow_blur equals `GLASS_SHADOW_BLUR.to_u32()`
   - Expected: light.shadow_blur equals `GLASS_SHADOW_BLUR.to_u32()`
   - Expected: obsidian.shadow_blur equals `GLASS_SHADOW_BLUR.to_u32()`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("all themes share the same shadow_blur")
val dark = GlassConfig.dark()
val light = GlassConfig.light()
val obsidian = GlassConfig.obsidian_dark()
expect(dark.shadow_blur).to_equal(GLASS_SHADOW_BLUR.to_u32())
expect(light.shadow_blur).to_equal(GLASS_SHADOW_BLUR.to_u32())
expect(obsidian.shadow_blur).to_equal(GLASS_SHADOW_BLUR.to_u32())
```

</details>

#### all themes share the same shadow_offset

- all themes share the same shadow_offset
   - Expected: dark.shadow_offset equals `GLASS_SHADOW_OFFSET.to_i32()`
   - Expected: light.shadow_offset equals `GLASS_SHADOW_OFFSET.to_i32()`
   - Expected: obsidian.shadow_offset equals `GLASS_SHADOW_OFFSET.to_i32()`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("all themes share the same shadow_offset")
val dark = GlassConfig.dark()
val light = GlassConfig.light()
val obsidian = GlassConfig.obsidian_dark()
expect(dark.shadow_offset).to_equal(GLASS_SHADOW_OFFSET.to_i32())
expect(light.shadow_offset).to_equal(GLASS_SHADOW_OFFSET.to_i32())
expect(obsidian.shadow_offset).to_equal(GLASS_SHADOW_OFFSET.to_i32())
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 30 |
| Active scenarios | 30 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


## Related Documentation

- **Design:** `doc/05_design/stitch_design_system.md`


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-UNIT`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `cfab1e132c1cad557cffc7a334aa0c9ae059a5f1de92acb1b426de528f0a6abc`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `cfab1e132c1cad557cffc7a334aa0c9ae059a5f1de92acb1b426de528f0a6abc`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `cfab1e132c1cad557cffc7a334aa0c9ae059a5f1de92acb1b426de528f0a6abc`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/unit/lib/common/glass_token_unification_spec.spl
mirror: doc/06_spec/unit/lib/common/glass_token_unification_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/unit/lib/common/glass_token_unification_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/unit/lib/common/glass_token_unification_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/unit/lib/common/glass_token_unification_spec.spl:81:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'surface_color matches GLASS_DARK_SURFACE' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/lib/common/glass_token_unification_spec.spl:87:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'surface_alpha matches GLASS_DARK_SURFACE_A' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/lib/common/glass_token_unification_spec.spl:93:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'blur_radius matches GLASS_BLUR_SURFACE' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
