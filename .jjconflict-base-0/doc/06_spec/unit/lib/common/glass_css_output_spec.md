# Glass CSS Output Specification

> AC-2: Theme system supports HTML+CSS output (Electron-like) from glass design tokens.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 29 | 29 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Glass CSS Output Specification

AC-2: Theme system supports HTML+CSS output (Electron-like) from glass design tokens.

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #GUI-THEME-SHARING |
| Category | Stdlib |
| Difficulty | 2/5 |
| Status | Draft |
| Requirements | N/A |
| Plan | N/A |
| Design | doc/05_design/stitch_design_system.md |
| Source | `test/unit/lib/common/glass_css_output_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

AC-2: Theme system supports HTML+CSS output (Electron-like) from glass
design tokens.

Verifies that:
- glass_tokens_to_css() emits all existing custom properties
- glass_tokens_to_css() emits new MD3 surface container custom properties
- glass_tokens_to_css() emits --glass-on-surface-variant
- generate_glass_css() produces a complete CSS string with :root block
- generate_glass_css() returns empty string for unknown themes
- Component CSS classes are present (widget-panel, glass-window, etc.)

## Key Concepts

| Concept | Description |
|---------|-------------|
| glass_tokens_to_css | Emits CSS custom properties from GlassDesignTokens |
| generate_glass_css | Full CSS entry point: :root vars + component styles |
| MD3 containers | --glass-surface-container-lowest through --glass-surface-container-highest |

## Scenarios

### glass_tokens_to_css existing properties

#### emits --glass-surface-primary

- emits --glass-surface-primary


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("emits --glass-surface-primary")
val tokens = GlassDesignTokens.dark()
val css = glass_tokens_to_css(tokens, StitchMetadata.glass())
expect(css).to_contain("--glass-surface-primary:")
```

</details>

#### emits --glass-text-primary

- emits --glass-text-primary


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("emits --glass-text-primary")
val tokens = GlassDesignTokens.dark()
val css = glass_tokens_to_css(tokens, StitchMetadata.glass())
expect(css).to_contain("--glass-text-primary:")
```

</details>

#### emits --glass-accent

- emits --glass-accent


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("emits --glass-accent")
val tokens = GlassDesignTokens.dark()
val css = glass_tokens_to_css(tokens, StitchMetadata.glass())
expect(css).to_contain("--glass-accent:")
```

</details>

#### emits --glass-error

- emits --glass-error


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("emits --glass-error")
val tokens = GlassDesignTokens.dark()
val css = glass_tokens_to_css(tokens, StitchMetadata.glass())
expect(css).to_contain("--glass-error:")
```

</details>

#### emits --glass-blur-surface

- emits --glass-blur-surface


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("emits --glass-blur-surface")
val tokens = GlassDesignTokens.dark()
val css = glass_tokens_to_css(tokens, StitchMetadata.glass())
expect(css).to_contain("--glass-blur-surface:")
```

</details>

#### emits --glass-radius-md

- emits --glass-radius-md


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("emits --glass-radius-md")
val tokens = GlassDesignTokens.dark()
val css = glass_tokens_to_css(tokens, StitchMetadata.glass())
expect(css).to_contain("--glass-radius-md:")
```

</details>

#### emits --glass-shadow-md

- emits --glass-shadow-md


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("emits --glass-shadow-md")
val tokens = GlassDesignTokens.dark()
val css = glass_tokens_to_css(tokens, StitchMetadata.glass())
expect(css).to_contain("--glass-shadow-md:")
```

</details>

#### emits --glass-spacing-md

- emits --glass-spacing-md


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("emits --glass-spacing-md")
val tokens = GlassDesignTokens.dark()
val css = glass_tokens_to_css(tokens, StitchMetadata.glass())
expect(css).to_contain("--glass-spacing-md:")
```

</details>

#### emits --glass-duration-fast

- emits --glass-duration-fast


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("emits --glass-duration-fast")
val tokens = GlassDesignTokens.dark()
val css = glass_tokens_to_css(tokens, StitchMetadata.glass())
expect(css).to_contain("--glass-duration-fast:")
```

</details>

### glass_tokens_to_css MD3 container properties

#### emits --glass-surface-container-lowest

- emits --glass-surface-container-lowest


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("emits --glass-surface-container-lowest")
val tokens = GlassDesignTokens.dark()
val css = glass_tokens_to_css(tokens, StitchMetadata.glass())
expect(css).to_contain("--glass-surface-container-lowest:")
```

</details>

#### emits --glass-surface-container-low

- emits --glass-surface-container-low


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("emits --glass-surface-container-low")
val tokens = GlassDesignTokens.dark()
val css = glass_tokens_to_css(tokens, StitchMetadata.glass())
expect(css).to_contain("--glass-surface-container-low:")
```

</details>

#### emits --glass-surface-container:

- emits --glass-surface-container:


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("emits --glass-surface-container:")
val tokens = GlassDesignTokens.dark()
val css = glass_tokens_to_css(tokens, StitchMetadata.glass())
expect(css).to_contain("--glass-surface-container:")
```

</details>

#### emits --glass-surface-container-high

- emits --glass-surface-container-high


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("emits --glass-surface-container-high")
val tokens = GlassDesignTokens.dark()
val css = glass_tokens_to_css(tokens, StitchMetadata.glass())
expect(css).to_contain("--glass-surface-container-high:")
```

</details>

#### emits --glass-surface-container-highest

- emits --glass-surface-container-highest


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("emits --glass-surface-container-highest")
val tokens = GlassDesignTokens.dark()
val css = glass_tokens_to_css(tokens, StitchMetadata.glass())
expect(css).to_contain("--glass-surface-container-highest:")
```

</details>

#### emits --glass-on-surface-variant

- emits --glass-on-surface-variant


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("emits --glass-on-surface-variant")
val tokens = GlassDesignTokens.dark()
val css = glass_tokens_to_css(tokens, StitchMetadata.glass())
expect(css).to_contain("--glass-on-surface-variant:")
```

</details>

### glass_tokens_to_css Obsidian theme values

#### contains Obsidian text color #E3E0F3

- contains Obsidian text color #E3E0F3


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("contains Obsidian text color #E3E0F3")
val tokens = GlassDesignTokens.obsidian_dark()
val css = glass_tokens_to_css(tokens, StitchMetadata.glass())
expect(css).to_contain("#E3E0F3")
```

</details>

#### contains Obsidian accent color #C6C6C8

- contains Obsidian accent color #C6C6C8


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("contains Obsidian accent color #C6C6C8")
val tokens = GlassDesignTokens.obsidian_dark()
val css = glass_tokens_to_css(tokens, StitchMetadata.glass())
expect(css).to_contain("#C6C6C8")
```

</details>

#### contains Obsidian surface rgba with 18,18,31

- contains Obsidian surface rgba with 18,18,31


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("contains Obsidian surface rgba with 18,18,31")
val tokens = GlassDesignTokens.obsidian_dark()
val css = glass_tokens_to_css(tokens, StitchMetadata.glass())
expect(css).to_contain("18,18,31")
```

</details>

### generate_glass_css full output

#### wraps tokens in :root block for glass_dark

- wraps tokens in :root block for glass_dark


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("wraps tokens in :root block for glass_dark")
val css = generate_glass_css("glass_dark")
expect(css).to_contain(":root")
```

</details>

#### includes component CSS for glass_dark

- includes component CSS for glass_dark


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("includes component CSS for glass_dark")
val css = generate_glass_css("glass_dark")
expect(css).to_contain(".widget-panel")
```

</details>

#### includes glass-window CSS

- includes glass-window CSS


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("includes glass-window CSS")
val css = generate_glass_css("glass_dark")
expect(css).to_contain(".glass-window")
```

</details>

#### includes glass-dock CSS

- includes glass-dock CSS


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("includes glass-dock CSS")
val css = generate_glass_css("glass_dark")
expect(css).to_contain(".glass-dock")
```

</details>

#### includes glass-titlebar CSS

- includes glass-titlebar CSS


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("includes glass-titlebar CSS")
val css = generate_glass_css("glass_dark")
expect(css).to_contain(".glass-titlebar")
```

</details>

#### includes glass-systembar CSS

- includes glass-systembar CSS


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("includes glass-systembar CSS")
val css = generate_glass_css("glass_dark")
expect(css).to_contain(".glass-systembar")
```

</details>

#### returns empty for unknown theme

- returns empty for unknown theme
   - Expected: css equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns empty for unknown theme")
val css = generate_glass_css("nonexistent_theme")
expect(css).to_equal("")
```

</details>

#### produces non-empty output for glass_light

- produces non-empty output for glass_light


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("produces non-empty output for glass_light")
val css = generate_glass_css("glass_light")
expect(css).to_contain(":root")
```

</details>

#### produces non-empty output for glass_obsidian_dark

- produces non-empty output for glass_obsidian_dark


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("produces non-empty output for glass_obsidian_dark")
val css = generate_glass_css("glass_obsidian_dark")
expect(css).to_contain(":root")
```

</details>

#### obsidian CSS contains MD3 container variables

- obsidian CSS contains MD3 container variables


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("obsidian CSS contains MD3 container variables")
val css = generate_glass_css("glass_obsidian_dark")
expect(css).to_contain("--glass-surface-container-lowest")
```

</details>

#### obsidian CSS contains backdrop-filter

- obsidian CSS contains backdrop-filter


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("obsidian CSS contains backdrop-filter")
val css = generate_glass_css("glass_obsidian_dark")
expect(css).to_contain("backdrop-filter")
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 29 |
| Active scenarios | 29 |
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

- Canonical SPipe generation for source `a0725eff7fea13482f663f354887af32cf06f0d3773d87880e2848479a6aec0f`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `a0725eff7fea13482f663f354887af32cf06f0d3773d87880e2848479a6aec0f`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `a0725eff7fea13482f663f354887af32cf06f0d3773d87880e2848479a6aec0f`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/unit/lib/common/glass_css_output_spec.spl
mirror: doc/06_spec/unit/lib/common/glass_css_output_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/unit/lib/common/glass_css_output_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/unit/lib/common/glass_css_output_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/unit/lib/common/glass_css_output_spec.spl:59:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'emits --glass-surface-primary' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/lib/common/glass_css_output_spec.spl:66:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'emits --glass-text-primary' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/lib/common/glass_css_output_spec.spl:73:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'emits --glass-accent' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
