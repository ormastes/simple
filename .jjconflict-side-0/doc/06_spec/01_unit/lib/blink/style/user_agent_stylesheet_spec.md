# Blink User-Agent Default Stylesheet

> Without ANY author CSS, a real browser still lays out `<div>` as a block box and `<span>` as inline, gives `<p>`/`<h1>`-`<h6>` real sizes and margins, and colours `<a>` blue. Before this module, blink's cascade had no such concept: `computed_style_default()` is the CSS *initial* value set, which is `display: inline` and `width`/`height: 0px` for every element regardless of tag — so an unstyled document rendered blank.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 11 | 11 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Blink User-Agent Default Stylesheet

Without ANY author CSS, a real browser still lays out `<div>` as a block box and `<span>` as inline, gives `<p>`/`<h1>`-`<h6>` real sizes and margins, and colours `<a>` blue. Before this module, blink's cascade had no such concept: `computed_style_default()` is the CSS *initial* value set, which is `display: inline` and `width`/`height: 0px` for every element regardless of tag — so an unstyled document rendered blank.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Browser / Blink |
| Status | Active |
| Source | `test/01_unit/lib/blink/style/user_agent_stylesheet_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Without ANY author CSS, a real browser still lays out `<div>` as a block box
and `<span>` as inline, gives `<p>`/`<h1>`-`<h6>` real sizes and margins, and
colours `<a>` blue. Before this module, blink's cascade had no such concept:
`computed_style_default()` is the CSS *initial* value set, which is
`display: inline` and `width`/`height: 0px` for every element regardless of
tag — so an unstyled document rendered blank.

`user_agent_stylesheet()` supplies a real `CssStyleSheet`, built through the
SAME `tokenize_css`/`parse_css` the document's own `<style>` text goes
through, and `merge_stylesheets` puts it in front of the document's rules so
any author rule — even one of equal selector specificity — wins.

@manual_section Browser Rendering

## Scenarios

### user_agent_stylesheet: non-vacuous parse

#### parses to a non-empty rule list

- parses to a non-empty rule list
- parse USER_AGENT_CSS the same way the document's own <style> is parsed
- expect more than a handful of rules — the source declares 20+ selectors
   - Expected: sheet.rules.len() > 20 is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("parses to a non-empty rule list")
step("parse USER_AGENT_CSS the same way the document's own <style> is parsed")
val sheet = user_agent_stylesheet()
step("expect more than a handful of rules — the source declares 20+ selectors")
expect(sheet.rules.len() > 20).to_equal(true)
```

</details>

#### carries no comma-grouped selector, which this engine's matcher cannot match

- carries no comma-grouped selector, which this engine's matcher cannot match
- scan every parsed rule's selector text for a literal comma
   - Expected: found_comma is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 17 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("carries no comma-grouped selector, which this engine's matcher cannot match")
step("scan every parsed rule's selector text for a literal comma")
# css_parser.selector.parse_selector has no selector-list support; a
# rule written as "div, span { ... }" would parse as ONE rule whose
# selector is the whole group and then never match anything. If this
# ever regresses, every UA default for the tags after the first comma
# silently stops applying — catch it here, not by staring at pixels.
val sheet = user_agent_stylesheet()
var i = 0
var found_comma = false
while i < sheet.rules.len():
    val sel = sheet.rules[i as i32].selector
    if sel.contains(","):
        found_comma = true
    i = i + 1
expect(found_comma).to_equal(false)
```

</details>

### user_agent_stylesheet: display defaults reach a real element

#### a bare <div> resolves to display: block

- a bare <div> resolves to display: block
- build a lone <div> and resolve it against the UA sheet with no author CSS
   - Expected: result.display == Display.Block is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("a bare <div> resolves to display: block")
step("build a lone <div> and resolve it against the UA sheet with no author CSS")
val (tree, el) = _one_element_tree("div")
val merged = merge_stylesheets(user_agent_stylesheet(), _empty_sheet())
val result = resolve_style(tree, el, computed_style_default(), merged)
expect(result.display == Display.Block).to_equal(true)
```

</details>

#### a bare <span> resolves to display: inline

- a bare <span> resolves to display: inline
- build a lone <span> and resolve it against the UA sheet with no author CSS
   - Expected: result.display == Display.Inline is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("a bare <span> resolves to display: inline")
step("build a lone <span> and resolve it against the UA sheet with no author CSS")
val (tree, el) = _one_element_tree("span")
val merged = merge_stylesheets(user_agent_stylesheet(), _empty_sheet())
val result = resolve_style(tree, el, computed_style_default(), merged)
expect(result.display == Display.Inline).to_equal(true)
```

</details>

#### sabotage check: a tag the UA sheet has no rule for stays at the CSS initial value

- sabotage check: a tag the UA sheet has no rule for stays at the CSS initial value
- resolve an <svg>, which USER_AGENT_CSS does not mention, against the UA sheet
- expect the CSS initial value (inline), proving the div/span result above is a real match, not every element defaulting to block
   - Expected: result.display == Display.Inline is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("sabotage check: a tag the UA sheet has no rule for stays at the CSS initial value")
step("resolve an <svg>, which USER_AGENT_CSS does not mention, against the UA sheet")
val (tree, el) = _one_element_tree("svg")
val merged = merge_stylesheets(user_agent_stylesheet(), _empty_sheet())
val result = resolve_style(tree, el, computed_style_default(), merged)
step("expect the CSS initial value (inline), proving the div/span result above is a real match, not every element defaulting to block")
expect(result.display == Display.Inline).to_equal(true)
```

</details>

#### an h1 gets a default font-size and vertical margins

- an h1 gets a default font-size and vertical margins
- resolve a lone <h1> against the UA sheet
   - Expected: result.display == Display.Block is true
   - Expected: result.font_size.value > 31.9 and result.font_size.value < 32.1 is true
   - Expected: result.font_size.unit equals `px`
   - Expected: result.margin_top.value > 20.9 and result.margin_top.value < 21.1 is true
   - Expected: result.margin_bottom.value > 20.9 and result.margin_bottom.value < 21.1 is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("an h1 gets a default font-size and vertical margins")
step("resolve a lone <h1> against the UA sheet")
val (tree, el) = _one_element_tree("h1")
val merged = merge_stylesheets(user_agent_stylesheet(), _empty_sheet())
val result = resolve_style(tree, el, computed_style_default(), merged)
expect(result.display == Display.Block).to_equal(true)
expect(result.font_size.value > 31.9 and result.font_size.value < 32.1).to_equal(true)
expect(result.font_size.unit).to_equal("px")
expect(result.margin_top.value > 20.9 and result.margin_top.value < 21.1).to_equal(true)
expect(result.margin_bottom.value > 20.9 and result.margin_bottom.value < 21.1).to_equal(true)
```

</details>

#### an <a> gets the default blue link colour

- an <a> gets the default blue link colour
- resolve a lone <a> against the UA sheet
   - Expected: result.color.b > 0.99 is true
   - Expected: result.color.r < 0.01 is true
   - Expected: result.color.g < 0.01 is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("an <a> gets the default blue link colour")
step("resolve a lone <a> against the UA sheet")
val (tree, el) = _one_element_tree("a")
val merged = merge_stylesheets(user_agent_stylesheet(), _empty_sheet())
val result = resolve_style(tree, el, computed_style_default(), merged)
expect(result.color.b > 0.99).to_equal(true)
expect(result.color.r < 0.01).to_equal(true)
expect(result.color.g < 0.01).to_equal(true)
```

</details>

### merge_stylesheets: the UA sheet is strictly lowest priority

#### an author type-selector rule of equal specificity overrides the UA default

- an author type-selector rule of equal specificity overrides the UA default
- author `div { display: inline }`, contradicting the UA default of block
- expect the author's inline to win, not the UA sheet's block
   - Expected: result.display == Display.Inline is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("an author type-selector rule of equal specificity overrides the UA default")
step("author `div { display: inline }`, contradicting the UA default of block")
val (tree, el) = _one_element_tree("div")
val author = _one_rule_sheet("div", "display", "inline")
val merged = merge_stylesheets(user_agent_stylesheet(), author)
val result = resolve_style(tree, el, computed_style_default(), merged)
step("expect the author's inline to win, not the UA sheet's block")
expect(result.display == Display.Inline).to_equal(true)
```

</details>

#### an author id-selector rule overrides the UA default on specificity alone

- an author id-selector rule overrides the UA default on specificity alone
- give the element id=go and author `#go { display: inline }`
   - Expected: result.display == Display.Inline is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("an author id-selector rule overrides the UA default on specificity alone")
step("give the element id=go and author `#go { display: inline }`")
var tree = dom_tree_new()
val el = tree.create_element("div")
tree.append_child(tree.root_id, el)
tree.set_attribute(el, "id", "go")
val author = _one_rule_sheet("#go", "display", "inline")
val merged = merge_stylesheets(user_agent_stylesheet(), author)
val result = resolve_style(tree, el, computed_style_default(), merged)
expect(result.display == Display.Inline).to_equal(true)
```

</details>

#### sabotage check: with no author rule the UA default alone still applies

- sabotage check: with no author rule the UA default alone still applies
- resolve the same <div> against the UA sheet merged with an empty author sheet
- expect block: proves the override above is really the author rule winning, not display defaulting to inline regardless
   - Expected: result.display == Display.Block is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("sabotage check: with no author rule the UA default alone still applies")
step("resolve the same <div> against the UA sheet merged with an empty author sheet")
val (tree, el) = _one_element_tree("div")
val merged = merge_stylesheets(user_agent_stylesheet(), _empty_sheet())
val result = resolve_style(tree, el, computed_style_default(), merged)
step("expect block: proves the override above is really the author rule winning, not display defaulting to inline regardless")
expect(result.display == Display.Block).to_equal(true)
```

</details>

#### merges rule counts additively: UA rules then document rules, nothing dropped

- merges rule counts additively: UA rules then document rules, nothing dropped
- merge the UA sheet with a two-rule author sheet
   - Expected: merged.rules.len() equals `ua.rules.len() + 2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("merges rule counts additively: UA rules then document rules, nothing dropped")
step("merge the UA sheet with a two-rule author sheet")
var ds: [CssDeclaration] = []
ds.push(CssDeclaration(property: "color", value: "red", important: false))
var rules: [CssStyleRule] = []
rules.push(CssStyleRule(selector: "div", declarations: ds))
rules.push(CssStyleRule(selector: "span", declarations: ds))
val author = CssStyleSheet(rules: rules, errors: [])
val ua = user_agent_stylesheet()
val merged = merge_stylesheets(ua, author)
expect(merged.rules.len()).to_equal(ua.rules.len() + 2)
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

- `REQ-SSPEC-LIB`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `0011b08e1f99c0f43c72c4b444fc6827de732d5c5676dc36a0c46a1d13bf4321`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `0011b08e1f99c0f43c72c4b444fc6827de732d5c5676dc36a0c46a1d13bf4321`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `0011b08e1f99c0f43c72c4b444fc6827de732d5c5676dc36a0c46a1d13bf4321`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/01_unit/lib/blink/style/user_agent_stylesheet_spec.spl
mirror: doc/06_spec/01_unit/lib/blink/style/user_agent_stylesheet_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/lib/blink/style/user_agent_stylesheet_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/lib/blink/style/user_agent_stylesheet_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/lib/blink/style/user_agent_stylesheet_spec.spl:73:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'parses to a non-empty rule list' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/blink/style/user_agent_stylesheet_spec.spl:82:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'carries no comma-grouped selector, which this engine's matcher cannot match' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/blink/style/user_agent_stylesheet_spec.spl:110:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'a bare <div> resolves to display: block' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
