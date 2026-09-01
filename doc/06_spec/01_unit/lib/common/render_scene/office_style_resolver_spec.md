# office_style_resolver_spec

> Office style resolver spec.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 11 | 11 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# office_style_resolver_spec

Office style resolver spec.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/common/render_scene/office_style_resolver_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

Office style resolver spec.

Verifies the shared style substrate (`std.common.render_scene.office_style_resolver`)
that maps office / markdown element tags and utility classes to resolved CSS
declarations and projects them to GUI (CSS text) and TUI (SGR codes). This is
the slice-2 spine of the LibreOffice suite program — a single default theme
drives both the terminal and graphical office surfaces.

All values are CSS value strings, so these assertions run on the interpreter
test runner without tripping the f64 nested-payload toolchain bug.

## Scenarios

### office style resolver: default theme

#### heading_1 is bold and 2em

- heading_1 is bold and 2em
   - Expected: style_value(h1, "font-weight") equals `bold`
   - Expected: style_value(h1, "font-size") equals `2em`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("heading_1 is bold and 2em")
val h1 = resolve_style("heading_1", [])
expect(style_value(h1, "font-weight")).to_equal("bold")
expect(style_value(h1, "font-size")).to_equal("2em")
```

</details>

#### quote is italic

- quote is italic
   - Expected: style_value(q, "font-style") equals `italic`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("quote is italic")
val q = resolve_style("quote", [])
expect(style_value(q, "font-style")).to_equal("italic")
```

</details>

#### paragraph and headings default unspecified text to Fira Code Nerd

- paragraph and headings default unspecified text to Fira Code Nerd
   - Expected: style_value(p, "font-family") equals `"Fira Code", "Liberation Mono", monospace`
   - Expected: style_value(h1, "font-family") equals `"Fira Code", "Liberation Mono", monospace`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("paragraph and headings default unspecified text to Fira Code Nerd")
val p = resolve_style("paragraph", [])
expect(style_value(p, "font-family")).to_equal("\"Fira Code\", \"Liberation Mono\", monospace")
val h1 = resolve_style("heading_1", [])
expect(style_value(h1, "font-family")).to_equal("\"Fira Code\", \"Liberation Mono\", monospace")
```

</details>

#### code_block uses a monospace family

- code_block uses a monospace family
   - Expected: style_value(c, "font-family") equals `monospace`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("code_block uses a monospace family")
val c = resolve_style("code_block", [])
expect(style_value(c, "font-family")).to_equal("monospace")
```

</details>

#### an unknown tag resolves to an empty block

- an unknown tag resolves to an empty block
   - Expected: style_to_css_text(u) equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("an unknown tag resolves to an empty block")
val u = resolve_style("nope", [])
expect(style_to_css_text(u)).to_equal("")
```

</details>

#### slide_title is large, bold, and centered

- slide_title is large, bold, and centered
   - Expected: style_value(t, "font-size") equals `2.5em`
   - Expected: style_value(t, "font-weight") equals `bold`
   - Expected: style_value(t, "text-align") equals `center`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("slide_title is large, bold, and centered")
val t = resolve_style("slide_title", [])
expect(style_value(t, "font-size")).to_equal("2.5em")
expect(style_value(t, "font-weight")).to_equal("bold")
expect(style_value(t, "text-align")).to_equal("center")
```

</details>

#### slide_bullet uses a disc list style

- slide_bullet uses a disc list style
   - Expected: style_value(b, "list-style") equals `disc`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("slide_bullet uses a disc list style")
val b = resolve_style("slide_bullet", [])
expect(style_value(b, "list-style")).to_equal("disc")
```

</details>

### office style resolver: class cascade
_Utility classes override the base element style, last class winning._

#### applies bold and italic utility classes to a paragraph

- applies bold and italic utility classes to a paragraph
   - Expected: style_value(p, "font-weight") equals `bold`
   - Expected: style_value(p, "font-style") equals `italic`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("applies bold and italic utility classes to a paragraph")
val p = resolve_style("paragraph", ["bold", "italic"])
expect(style_value(p, "font-weight")).to_equal("bold")
expect(style_value(p, "font-style")).to_equal("italic")
```

</details>

### office style resolver: surface projections
_A resolved style projects to GUI CSS text and a TUI SGR parameter string._

#### projects heading_1 to a CSS declaration string

- projects heading_1 to a CSS declaration string


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("projects heading_1 to a CSS declaration string")
val h1 = resolve_style("heading_1", [])
expect(style_to_css_text(h1)).to_contain("font-weight: bold;")
```

</details>

#### projects bold+italic to the SGR string 1;3

- projects bold+italic to the SGR string 1;3
   - Expected: style_to_sgr(p) equals `1;3`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("projects bold+italic to the SGR string 1;3")
val p = resolve_style("paragraph", ["bold", "italic"])
expect(style_to_sgr(p)).to_equal("1;3")
```

</details>

#### projects an unstyled element to an empty SGR string

- projects an unstyled element to an empty SGR string
   - Expected: style_to_sgr(img) equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("projects an unstyled element to an empty SGR string")
val img = resolve_style("image", [])
expect(style_to_sgr(img)).to_equal("")
```

</details>

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

- `REQ-SSPEC-UNIT`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `6a8f4f478afa3dab04406cf08df84408086c721eb95f034e75eaaa66c753fd87`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `6a8f4f478afa3dab04406cf08df84408086c721eb95f034e75eaaa66c753fd87`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `6a8f4f478afa3dab04406cf08df84408086c721eb95f034e75eaaa66c753fd87`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/01_unit/lib/common/render_scene/office_style_resolver_spec.spl
mirror: doc/06_spec/01_unit/lib/common/render_scene/office_style_resolver_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/lib/common/render_scene/office_style_resolver_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/lib/common/render_scene/office_style_resolver_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/lib/common/render_scene/office_style_resolver_spec.spl:27:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'heading_1 is bold and 2em' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/common/render_scene/office_style_resolver_spec.spl:34:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'quote is italic' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/common/render_scene/office_style_resolver_spec.spl:40:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'paragraph and headings default unspecified text to Fira Code Nerd' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
