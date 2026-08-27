# simple_web_css_cascade_spec

> Simple Web CSS Cascade Spec

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 11 | 11 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# simple_web_css_cascade_spec

Simple Web CSS Cascade Spec

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/02_integration/rendering/simple_web_css_cascade_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

Simple Web CSS Cascade Spec

Focused coverage for CSS candidate ordering in the pure-Simple HTML layout
renderer.

@tag: rendering, simple-web, css, cascade, perf
@cover src/lib/gc_async_mut/gpu/browser_engine/simple_web_html_layout_renderer.spl 10%

## Scenarios

### simple web css cascade

#### gives attribute selectors class-level specificity in canonical pixels

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- gives attribute selectors class-level specificity in canonical pixels
- Render a fixed red attribute target against a later blue type rule
- Keep the higher-specificity attribute color and untouched canvas
   - Expected: pixels.len() equals `384`
   - Expected: pixels[2 + 2 * 24] equals `0xffef4444u32`
   - Expected: pixels[20 + 12 * 24] equals `0xffffffffu32`


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("gives attribute selectors class-level specificity in canonical pixels")
step("Render a fixed red attribute target against a later blue type rule")
val html = "<html><head><style>" +
    "html,body{margin:0;padding:0;background:#fff}" +
    "[data-tone]{width:12px;height:8px;background:#ef4444}" +
    "div{{background:#3b82f6}}" +
    "</style></head><body><div id=\"target\" data-tone></div></body></html>"
val pixels = simple_web_render_html_to_pixels_with_engine2d_backend(
    html, 24, 16, "software"
)
step("Keep the higher-specificity attribute color and untouched canvas")
expect(pixels.len()).to_equal(384)
expect(pixels[2 + 2 * 24]).to_equal(0xffef4444u32)
expect(pixels[20 + 12 * 24]).to_equal(0xffffffffu32)
```

</details>

#### keeps higher specificity after candidate merge sorting

- keeps higher specificity after candidate merge sorting
- Build rules where a lower-specificity class rule appears after a higher-specificity compound rule
- Resolve the target height through computed style
- Assert the higher-specificity selector still wins
   - Expected: height equals `33`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("keeps higher specificity after candidate merge sorting")
step("Build rules where a lower-specificity class rule appears after a higher-specificity compound rule")
val html = _cascade_fixture("div.target{height:33px}.target{height:21px}")
step("Resolve the target height through computed style")
val height = simple_web_layout_debug_style_by_id(html, "target", "height")
step("Assert the higher-specificity selector still wins")
expect(height).to_equal("33")
```

</details>

#### keeps source order for equal specificity candidates

- keeps source order for equal specificity candidates
- Build two equal-specificity class rules that both match the target
- Resolve the target height through computed style
- Assert the later equal-specificity rule wins
   - Expected: height equals `29`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("keeps source order for equal specificity candidates")
step("Build two equal-specificity class rules that both match the target")
val html = _cascade_fixture(".target{height:17px}.hot{height:29px}")
step("Resolve the target height through computed style")
val height = simple_web_layout_debug_style_by_id(html, "target", "height")
step("Assert the later equal-specificity rule wins")
expect(height).to_equal("29")
```

</details>

#### deduplicates a selector-list rule reached through tag and class buckets

- deduplicates a selector-list rule reached through tag and class buckets
- Build a selector-list rule that can enter through both tag and class buckets
- Resolve the target height through computed style
- Assert the later class rule still wins after the selector-list rule is merged once
   - Expected: height equals `23`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("deduplicates a selector-list rule reached through tag and class buckets")
step("Build a selector-list rule that can enter through both tag and class buckets")
val html = _cascade_fixture("div,.target{height:41px}.hot{height:23px}")
step("Resolve the target height through computed style")
val height = simple_web_layout_debug_style_by_id(html, "target", "height")
step("Assert the later class rule still wins after the selector-list rule is merged once")
expect(height).to_equal("23")
```

</details>

#### uses specificity from the selector-list branch that matched

- uses specificity from the selector-list branch that matched
- Build a selector list whose unmatched ID branch is more specific than its matching tag branch
- Resolve the target height through computed style
- Assert the later class beats the matching tag branch
   - Expected: height equals `23`
- Assert the highest-specificity branch wins when multiple branches match
   - Expected: simple_web_layout_debug_style_by_id(multiple, "target", "height") equals `41`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("uses specificity from the selector-list branch that matched")
step("Build a selector list whose unmatched ID branch is more specific than its matching tag branch")
val html = _cascade_fixture("#missing,div{height:41px}.hot{height:23px}")
step("Resolve the target height through computed style")
val height = simple_web_layout_debug_style_by_id(html, "target", "height")
step("Assert the later class beats the matching tag branch")
expect(height).to_equal("23")
val multiple = _cascade_fixture("#target,div{height:41px}.hot{height:23px}")
step("Assert the highest-specificity branch wins when multiple branches match")
expect(simple_web_layout_debug_style_by_id(multiple, "target", "height")).to_equal("41")
```

</details>

#### retains ordinary translucent backdrop CSS in the computed Style

- retains ordinary translucent backdrop CSS in the computed Style
- Build ordinary backdrop CSS with an alpha surface, a normalized linear gradient, and a radial layer stack
- Resolve the material fields through the normal CSS cascade
   - Expected: simple_web_layout_debug_style_by_id(html, "target", "background_color") equals `2148676694`
   - Expected: simple_web_layout_debug_style_by_id(html, "target", "background_gradient_from") equals `4279312947`
   - Expected: simple_web_layout_debug_style_by_id(html, "target", "background_gradient_to") equals `4282668390`
   - Expected: simple_web_layout_debug_style_by_id(html, "target", "backdrop_filter_raw") equals `blur(4px) saturate(120%)`
   - Expected: simple_web_layout_debug_style_by_id(html, "layers", "background_layers_raw") equals ``
   - Expected: simple_web_layout_debug_style_by_id(html, "layers", "background_color") equals `4279246896`
   - Expected: simple_web_layout_debug_style_by_id(html, "layers", "backdrop_filter_raw") equals `blur(2px)`


<details>
<summary>Executable SSpec</summary>

Runnable source: 18 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("retains ordinary translucent backdrop CSS in the computed Style")
step("Build ordinary backdrop CSS with an alpha surface, a normalized linear gradient, and a radial layer stack")
val html = "<html><head><style>" +
    "#target{background-color:rgba(18,52,86,0.5);background-image:linear-gradient(#112233,#445566);backdrop-filter:blur(4px) saturate(120%)}" +
    "#layers{background:radial-gradient(#010203,#040506),#102030;backdrop-filter:blur(2px)}" +
    "</style></head><body><div id=\"target\">row</div><div id=\"layers\">layers</div></body></html>"
step("Resolve the material fields through the normal CSS cascade")
expect(simple_web_layout_debug_style_by_id(html, "target", "background_color")).to_equal("2148676694")
expect(simple_web_layout_debug_style_by_id(html, "target", "background_gradient_from")).to_equal("4279312947")
expect(simple_web_layout_debug_style_by_id(html, "target", "background_gradient_to")).to_equal("4282668390")
expect(simple_web_layout_debug_style_by_id(html, "target", "backdrop_filter_raw")).to_equal("blur(4px) saturate(120%)")
# GAP-2 (doc/03_plan/ui/unified_2d_engine/drawir_feature_gap_2026-07-31.md,
# commit 184aded7e3f): `background: radial-gradient(..), <colour>` is now
# TYPED (radial stops + base colour), no longer a raw rejection witness.
expect(simple_web_layout_debug_style_by_id(html, "layers", "background_layers_raw")).to_equal("")
expect(simple_web_layout_debug_style_by_id(html, "layers", "background_color")).to_equal("4279246896")
expect(simple_web_layout_debug_style_by_id(html, "layers", "backdrop_filter_raw")).to_equal("blur(2px)")
```

</details>

#### preserves Aetheric shorthand base and gradient stop alpha in Style

- preserves Aetheric shorthand base and gradient stop alpha in Style
- Build the Aetheric translucent surface through the background shorthand
- Inspect the raw ARGB material values after shorthand parsing
   - Expected: simple_web_layout_debug_style_by_id(html, "aetheric", "background_color") equals `3424591649`
   - Expected: simple_web_layout_debug_style_by_id(html, "aetheric", "background_gradient_from") equals `352321535`
   - Expected: simple_web_layout_debug_style_by_id(html, "aetheric", "background_gradient_to") equals `117440511`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("preserves Aetheric shorthand base and gradient stop alpha in Style")
step("Build the Aetheric translucent surface through the background shorthand")
val html = "<html><head><style>#aetheric{background:linear-gradient(180deg,rgba(255,255,255,0.08),rgba(255,255,255,0.025)),rgba(31,31,33,0.80)}</style></head><body><div id=\"aetheric\"></div></body></html>"
step("Inspect the raw ARGB material values after shorthand parsing")
expect(simple_web_layout_debug_style_by_id(html, "aetheric", "background_color")).to_equal("3424591649")
expect(simple_web_layout_debug_style_by_id(html, "aetheric", "background_gradient_from")).to_equal("352321535")
expect(simple_web_layout_debug_style_by_id(html, "aetheric", "background_gradient_to")).to_equal("117440511")
```

</details>

#### normalizes one typed linear image and retains unsupported image syntax as a rejection witness

- normalizes one typed linear image and retains unsupported image syntax as a rejection witness
- Build exact, radial, multiple, URL, unknown, malformed, override, and reset image declarations
- Inspect the canonical typed pair and every unsupported raw witness
   - Expected: simple_web_layout_debug_style_by_id(html, "single", "background_layers_raw") equals ``
   - Expected: simple_web_layout_debug_style_by_id(html, "single", "background_gradient_from") equals `4279312947`
   - Expected: simple_web_layout_debug_style_by_id(html, "single", "background_gradient_to") equals `4282668390`
   - Expected: simple_web_layout_debug_style_by_id(html, "radial", "background_layers_raw") equals ``
   - Expected: simple_web_layout_debug_style_by_id(html, "multiple", "background_layers_raw") equals `linear-gradient(#112233,#445566),linear-gradient(#778899,#aabbcc)`
   - Expected: simple_web_layout_debug_style_by_id(html, "url", "background_layers_raw") equals ``
   - Expected: simple_web_layout_debug_style_by_id(html, "url", "background_image_uri") equals `hero.png`
   - Expected: simple_web_layout_debug_style_by_id(html, "unknown", "background_layers_raw") equals `conic-gradient(#112233,#445566)`
   - Expected: simple_web_layout_debug_style_by_id(html, "malformed", "background_layers_raw") equals `linear-gradient(#112233)`
   - Expected: simple_web_layout_debug_style_by_id(html, "override", "background_layers_raw") equals ``
   - Expected: simple_web_layout_debug_style_by_id(html, "override", "background_gradient_from") equals `0`
   - Expected: simple_web_layout_debug_style_by_id(html, "override", "background_gradient_to") equals `0`
   - Expected: simple_web_layout_debug_style_by_id(html, "reset", "background_layers_raw") equals ``
   - Expected: simple_web_layout_debug_style_by_id(html, "reset", "background_gradient_from") equals `0`
   - Expected: simple_web_layout_debug_style_by_id(html, "reset", "background_gradient_to") equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 36 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("normalizes one typed linear image and retains unsupported image syntax as a rejection witness")
step("Build exact, radial, multiple, URL, unknown, malformed, override, and reset image declarations")
val html = "<html><head><style>" +
    "#single{background-image:linear-gradient(#112233,#445566)}" +
    "#radial{background-image:radial-gradient(#112233,#445566)}" +
    "#multiple{background:linear-gradient(#112233,#445566),linear-gradient(#778899,#aabbcc)}" +
    "#url{background-image:url(hero.png)}" +
    "#unknown{background-image:conic-gradient(#112233,#445566)}" +
    "#malformed{background-image:linear-gradient(#112233)}" +
    "#override{background-image:linear-gradient(#112233,#445566);background-image:radial-gradient(#778899,#aabbcc)}" +
    "#reset{background-image:radial-gradient(#112233,#445566);background-image:none}" +
    "</style></head><body>" +
    "<div id=\"single\"></div><div id=\"radial\"></div><div id=\"multiple\"></div>" +
    "<div id=\"url\"></div><div id=\"unknown\"></div><div id=\"malformed\"></div>" +
    "<div id=\"override\"></div><div id=\"reset\"></div>" +
    "</body></html>"
step("Inspect the canonical typed pair and every unsupported raw witness")
expect(simple_web_layout_debug_style_by_id(html, "single", "background_layers_raw")).to_equal("")
expect(simple_web_layout_debug_style_by_id(html, "single", "background_gradient_from")).to_equal("4279312947")
expect(simple_web_layout_debug_style_by_id(html, "single", "background_gradient_to")).to_equal("4282668390")
# GAP-2: a single radial-gradient layer is now typed, not a raw witness.
expect(simple_web_layout_debug_style_by_id(html, "radial", "background_layers_raw")).to_equal("")
expect(simple_web_layout_debug_style_by_id(html, "multiple", "background_layers_raw")).to_equal("linear-gradient(#112233,#445566),linear-gradient(#778899,#aabbcc)")
# An exact url(...) layer is typed into background_image_uri, not kept raw.
expect(simple_web_layout_debug_style_by_id(html, "url", "background_layers_raw")).to_equal("")
expect(simple_web_layout_debug_style_by_id(html, "url", "background_image_uri")).to_equal("hero.png")
expect(simple_web_layout_debug_style_by_id(html, "unknown", "background_layers_raw")).to_equal("conic-gradient(#112233,#445566)")
expect(simple_web_layout_debug_style_by_id(html, "malformed", "background_layers_raw")).to_equal("linear-gradient(#112233)")
# GAP-2: the overriding radial layer is typed; from/to stay 0 (stop list carries it).
expect(simple_web_layout_debug_style_by_id(html, "override", "background_layers_raw")).to_equal("")
expect(simple_web_layout_debug_style_by_id(html, "override", "background_gradient_from")).to_equal("0")
expect(simple_web_layout_debug_style_by_id(html, "override", "background_gradient_to")).to_equal("0")
expect(simple_web_layout_debug_style_by_id(html, "reset", "background_layers_raw")).to_equal("")
expect(simple_web_layout_debug_style_by_id(html, "reset", "background_gradient_from")).to_equal("0")
expect(simple_web_layout_debug_style_by_id(html, "reset", "background_gradient_to")).to_equal("0")
```

</details>

#### keeps the named WM solid fallback opaque without an explicit composited mode

- keeps the named WM solid fallback opaque without an explicit composited mode
- Build a WM-decorated panel without the explicit CPU-composited material mode
- Resolve the fallback after the normal cascade
   - Expected: simple_web_layout_debug_style_by_id(html, "target", "background_color") equals `4279246896`
   - Expected: simple_web_layout_debug_style_by_id(html, "target", "background_gradient_from") equals `0`
   - Expected: simple_web_layout_debug_style_by_id(html, "target", "background_gradient_to") equals `0`
   - Expected: simple_web_layout_debug_style_by_id(html, "target", "backdrop_filter_raw") equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("keeps the named WM solid fallback opaque without an explicit composited mode")
step("Build a WM-decorated panel without the explicit CPU-composited material mode")
val html = "<html><head><style>#target{background-color:rgba(18,52,86,0.5);background-image:linear-gradient(#112233,#445566);backdrop-filter:blur(4px)}</style></head><body><div id=\"target\" data-wm-theme-fallback=\"solid-material\" data-wm-theme-bg=\"#102030\">row</div></body></html>"
step("Resolve the fallback after the normal cascade")
expect(simple_web_layout_debug_style_by_id(html, "target", "background_color")).to_equal("4279246896")
expect(simple_web_layout_debug_style_by_id(html, "target", "background_gradient_from")).to_equal("0")
expect(simple_web_layout_debug_style_by_id(html, "target", "background_gradient_to")).to_equal("0")
expect(simple_web_layout_debug_style_by_id(html, "target", "backdrop_filter_raw")).to_equal("")
```

</details>

#### preserves authored CSS for the exact CPU-composited WM material mode

- preserves authored CSS for the exact CPU-composited WM material mode
- Build a WM-decorated panel that explicitly opts into the CPU-composited material mode
- Resolve the authored material fields without the named solid rewrite
   - Expected: simple_web_layout_debug_style_by_id(html, "target", "background_color") equals `2148676694`
   - Expected: simple_web_layout_debug_style_by_id(html, "target", "background_gradient_from") equals `4279312947`
   - Expected: simple_web_layout_debug_style_by_id(html, "target", "background_gradient_to") equals `4282668390`
   - Expected: simple_web_layout_debug_style_by_id(html, "target", "backdrop_filter_raw") equals `blur(4px)`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("preserves authored CSS for the exact CPU-composited WM material mode")
step("Build a WM-decorated panel that explicitly opts into the CPU-composited material mode")
val html = "<html><head><style>#target{background-color:rgba(18,52,86,0.5);background-image:linear-gradient(#112233,#445566);backdrop-filter:blur(4px)}</style></head><body><div id=\"target\" data-wm-theme-fallback=\"solid-material\" data-wm-theme-bg=\"#102030\" data-wm-theme-material-mode=\"engine2d-cpu-composited-material-v1\">row</div></body></html>"
step("Resolve the authored material fields without the named solid rewrite")
expect(simple_web_layout_debug_style_by_id(html, "target", "background_color")).to_equal("2148676694")
expect(simple_web_layout_debug_style_by_id(html, "target", "background_gradient_from")).to_equal("4279312947")
expect(simple_web_layout_debug_style_by_id(html, "target", "background_gradient_to")).to_equal("4282668390")
expect(simple_web_layout_debug_style_by_id(html, "target", "backdrop_filter_raw")).to_equal("blur(4px)")
```

</details>

#### rejects a whitespace-padded CPU-composited WM material mode

- rejects a whitespace-padded CPU-composited WM material mode
- Build a WM panel whose opt-in token is not byte-exact
- Resolve the named opaque fallback instead of accepting the padded token


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("rejects a whitespace-padded CPU-composited WM material mode")
step("Build a WM panel whose opt-in token is not byte-exact")
val html = "<html><head><style>#target{background-color:rgba(18,52,86,0.5);background-image:linear-gradient(#112233,#445566);backdrop-filter:blur(4px)}</style></head><body><div id=\"target\" data-wm-theme-fallback=\"solid-material\" data-wm-theme-bg=\"#102030\" data-wm-theme-material-mode=\" engine2d-cpu-composited-material-v1 \">row</div></body></html>"
step("Resolve the named opaque fallback instead of accepting the padded token")
expect(simple_web_layout_debug_style_by_id(
    html, "target", "background_color")).to_equal("4279246896")
expect(simple_web_layout_debug_style_by_id(
    html, "target", "background_gradient_from")).to_equal("0")
expect(simple_web_layout_debug_style_by_id(
    html, "target", "background_gradient_to")).to_equal("0")
expect(simple_web_layout_debug_style_by_id(
    html, "target", "backdrop_filter_raw")).to_equal("")
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

- `REQ-SSPEC-INTEGRATION`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `91f3407bb0b6b0d3b32aa5e3040d0e2d7f4aae92ffef25fee941735c2251c219`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `91f3407bb0b6b0d3b32aa5e3040d0e2d7f4aae92ffef25fee941735c2251c219`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `91f3407bb0b6b0d3b32aa5e3040d0e2d7f4aae92ffef25fee941735c2251c219`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **90/100**; effective score: **90/100**; blockers: **0**.

SSpec documentization score: 90/100
source: test/02_integration/rendering/simple_web_css_cascade_spec.spl
mirror: doc/06_spec/02_integration/rendering/simple_web_css_cascade_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=90
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/02_integration/rendering/simple_web_css_cascade_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/02_integration/rendering/simple_web_css_cascade_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/02_integration/rendering/simple_web_css_cascade_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-10): 1 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/02_integration/rendering/simple_web_css_cascade_spec.spl:29:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'gives attribute selectors class-level specificity in canonical pixels' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/02_integration/rendering/simple_web_css_cascade_spec.spl:46:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'keeps higher specificity after candidate merge sorting' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/02_integration/rendering/simple_web_css_cascade_spec.spl:56:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'keeps source order for equal specificity candidates' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
