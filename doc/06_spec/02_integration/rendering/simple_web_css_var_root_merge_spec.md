# simple_web_css_var_root_merge_spec

> Simple Web CSS :root Variable Merge Spec

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 7 | 7 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# simple_web_css_var_root_merge_spec

Simple Web CSS :root Variable Merge Spec

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/02_integration/rendering/simple_web_css_var_root_merge_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

Simple Web CSS :root Variable Merge Spec

Regression coverage for CSS custom properties declared across several `:root`
blocks, and for the typed material that a themed panel rule must still produce
after those variables are substituted.

The SimpleOS `aetheric_dark` theme composes its stylesheet from several
fragments, so the shipped sheet contains more than one `:root` block and ends
with an empty one. A reader of the composed sheet must still see every declared
custom property: a later `:root` block contributes and overrides individual
names, it never replaces the whole custom-property table. When
`--app-surface: rgba(31,31,33,0.80)` fails to resolve, the panel's two-layer
`background` shorthand degrades to a gradient plus a dangling comma, the typed
gradient stops stay zero, the raw layer list is retained, and the window manager
rejects the frame for having no admitted material.

@tag: rendering, simple-web, css, custom-properties, theme
@cover src/lib/gc_async_mut/gpu/browser_engine/simple_web_html_layout_renderer_core.spl 5%

## Scenarios

### simple web css :root variable merge

#### resolves a variable declared by an earlier root block

- resolves a variable declared by an earlier root block
- Author a root block ahead of the rule that consumes its variable
- Resolve the computed height through the Simple Web style path
   - Expected: simple_web_layout_debug_style_by_id(html, "target", "height") equals `27`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("resolves a variable declared by an earlier root block")
step("Author a root block ahead of the rule that consumes its variable")
val html = _sheet(
    ":root{--panel-height:27px}.target{height:var(--panel-height)}",
    "<div id=\"target\" class=\"target\">row</div>"
)
step("Resolve the computed height through the Simple Web style path")
expect(simple_web_layout_debug_style_by_id(html, "target", "height")).to_equal("27")
```

</details>

#### keeps earlier variables alive when a later empty root block follows

- keeps earlier variables alive when a later empty root block follows
- Author the composed-theme shape: a populated root block, the consuming rule, then a trailing empty root block
- Resolve the computed height after the empty root block is parsed
   - Expected: simple_web_layout_debug_style_by_id(html, "target", "height") equals `27`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("keeps earlier variables alive when a later empty root block follows")
step("Author the composed-theme shape: a populated root block, the consuming rule, then a trailing empty root block")
val html = _sheet(
    ":root{--panel-height:27px}.target{height:var(--panel-height)}:root{}",
    "<div id=\"target\" class=\"target\">row</div>"
)
step("Resolve the computed height after the empty root block is parsed")
expect(simple_web_layout_debug_style_by_id(html, "target", "height")).to_equal("27")
```

</details>

#### merges variables contributed by separate root blocks

- merges variables contributed by separate root blocks
- Author two root blocks that each declare a different variable
- Resolve both consumers and confirm neither block wiped the other
   - Expected: simple_web_layout_debug_style_by_id(html, "head", "height") equals `11`
   - Expected: simple_web_layout_debug_style_by_id(html, "body", "height") equals `13`


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("merges variables contributed by separate root blocks")
step("Author two root blocks that each declare a different variable")
val html = _sheet(
    ":root{--head-height:11px}" +
    ":root{--body-height:13px}" +
    "#head{height:var(--head-height)}#body{height:var(--body-height)}",
    "<div id=\"head\">head</div><div id=\"body\">body</div>"
)
step("Resolve both consumers and confirm neither block wiped the other")
expect(simple_web_layout_debug_style_by_id(html, "head", "height")).to_equal("11")
expect(simple_web_layout_debug_style_by_id(html, "body", "height")).to_equal("13")
```

</details>

#### lets a later root block override one name without dropping the others

- lets a later root block override one name without dropping the others
- Author a second root block that redeclares one of three variables
- Confirm the override wins for its own name and the untouched names survive
   - Expected: simple_web_layout_debug_style_by_id(html, "a", "height") equals `11`
   - Expected: simple_web_layout_debug_style_by_id(html, "b", "height") equals `19`
   - Expected: simple_web_layout_debug_style_by_id(html, "c", "height") equals `23`


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("lets a later root block override one name without dropping the others")
step("Author a second root block that redeclares one of three variables")
val html = _sheet(
    ":root{--a-height:11px;--b-height:13px}" +
    ":root{--b-height:19px;--c-height:23px}" +
    "#a{height:var(--a-height)}#b{height:var(--b-height)}#c{height:var(--c-height)}",
    "<div id=\"a\">a</div><div id=\"b\">b</div><div id=\"c\">c</div>"
)
step("Confirm the override wins for its own name and the untouched names survive")
expect(simple_web_layout_debug_style_by_id(html, "a", "height")).to_equal("11")
expect(simple_web_layout_debug_style_by_id(html, "b", "height")).to_equal("19")
expect(simple_web_layout_debug_style_by_id(html, "c", "height")).to_equal("23")
```

</details>

#### substitutes a comma-bearing variable as one background layer

- substitutes a comma-bearing variable as one background layer
- Declare a surface colour whose own value contains commas and use it as the base layer of a two-layer shorthand
- Inspect the normalized layer list: gradient plus base colour, no empty trailing segment
   - Expected: simple_web_layout_debug_style_by_id(html, "panel", "background_layers_raw") equals ``
   - Expected: simple_web_layout_debug_style_by_id(html, "panel", "background_color") equals `2148144158`
   - Expected: simple_web_layout_debug_style_by_id(html, "panel", "background_gradient_from") equals `4279312947`
   - Expected: simple_web_layout_debug_style_by_id(html, "panel", "background_gradient_to") equals `4282668390`


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("substitutes a comma-bearing variable as one background layer")
step("Declare a surface colour whose own value contains commas and use it as the base layer of a two-layer shorthand")
val html = _sheet(
    ":root{--panel-base:rgba(10,20,30,0.5)}" +
    "#panel{background:linear-gradient(#112233,#445566),var(--panel-base)}",
    "<div id=\"panel\">panel</div>"
)
step("Inspect the normalized layer list: gradient plus base colour, no empty trailing segment")
expect(simple_web_layout_debug_style_by_id(html, "panel", "background_layers_raw")).to_equal("")
expect(simple_web_layout_debug_style_by_id(html, "panel", "background_color")).to_equal("2148144158")
expect(simple_web_layout_debug_style_by_id(html, "panel", "background_gradient_from")).to_equal("4279312947")
expect(simple_web_layout_debug_style_by_id(html, "panel", "background_gradient_to")).to_equal("4282668390")
```

</details>

#### normalizes the themed panel rule to typed material after variable substitution

- normalizes the themed panel rule to typed material after variable substitution
- Author the aetheric_dark surface variable, the shipped panel rule, and the theme's trailing empty root block
- Read the base surface: the resolved variable, never the gradient's first stop
   - Expected: simple_web_layout_debug_style_by_id(html, "panel", "background_color") equals `3424591649`
- Read the typed gradient stops carried by the first layer
   - Expected: simple_web_layout_debug_style_by_id(html, "panel", "background_gradient_from") equals `352321535`
   - Expected: simple_web_layout_debug_style_by_id(html, "panel", "background_gradient_to") equals `117440511`
- Confirm nothing is left as a raw layer, which is what the CPU material admission requires
   - Expected: simple_web_layout_debug_style_by_id(html, "panel", "background_layers_raw") equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("normalizes the themed panel rule to typed material after variable substitution")
step("Author the aetheric_dark surface variable, the shipped panel rule, and the theme's trailing empty root block")
val html = _sheet(
    ":root{--app-surface: rgba(31,31,33,0.80)}" +
    _widget_panel_rule() +
    ":root{}",
    _panel_body()
)
step("Read the base surface: the resolved variable, never the gradient's first stop")
expect(simple_web_layout_debug_style_by_id(html, "panel", "background_color")).to_equal("3424591649")
step("Read the typed gradient stops carried by the first layer")
expect(simple_web_layout_debug_style_by_id(html, "panel", "background_gradient_from")).to_equal("352321535")
expect(simple_web_layout_debug_style_by_id(html, "panel", "background_gradient_to")).to_equal("117440511")
step("Confirm nothing is left as a raw layer, which is what the CPU material admission requires")
expect(simple_web_layout_debug_style_by_id(html, "panel", "background_layers_raw")).to_equal("")
```

</details>

#### refuses typed material when the surface variable does not exist

- refuses typed material when the surface variable does not exist
- Author the same panel rule against a variable no root block declares
- Confirm the unresolvable reference fails closed: no typed gradient is published, so material admission cannot succeed
   - Expected: simple_web_layout_debug_style_by_id(html, "panel", "background_gradient_from") equals `0`
   - Expected: simple_web_layout_debug_style_by_id(html, "panel", "background_gradient_to") equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("refuses typed material when the surface variable does not exist")
step("Author the same panel rule against a variable no root block declares")
val html = _sheet(
    ":root{--other-surface: rgba(31,31,33,0.80)}" +
    ".widget-panel{background: linear-gradient(180deg, rgba(255,255,255,0.08), rgba(255,255,255,0.025)), var(--app-surface)}",
    _panel_body()
)
step("Confirm the unresolvable reference fails closed: no typed gradient is published, so material admission cannot succeed")
expect(simple_web_layout_debug_style_by_id(html, "panel", "background_gradient_from")).to_equal("0")
expect(simple_web_layout_debug_style_by_id(html, "panel", "background_gradient_to")).to_equal("0")
```

</details>

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

- `REQ-SSPEC-INTEGRATION`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `e08727b0d2369f73e654a8cc2decb59ad5a92dbd0e73715d0db337bc35cced74`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `e08727b0d2369f73e654a8cc2decb59ad5a92dbd0e73715d0db337bc35cced74`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `e08727b0d2369f73e654a8cc2decb59ad5a92dbd0e73715d0db337bc35cced74`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/02_integration/rendering/simple_web_css_var_root_merge_spec.spl
mirror: doc/06_spec/02_integration/rendering/simple_web_css_var_root_merge_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/02_integration/rendering/simple_web_css_var_root_merge_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/02_integration/rendering/simple_web_css_var_root_merge_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/02_integration/rendering/simple_web_css_var_root_merge_spec.spl:49:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'resolves a variable declared by an earlier root block' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/02_integration/rendering/simple_web_css_var_root_merge_spec.spl:60:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'keeps earlier variables alive when a later empty root block follows' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/02_integration/rendering/simple_web_css_var_root_merge_spec.spl:71:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'merges variables contributed by separate root blocks' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
