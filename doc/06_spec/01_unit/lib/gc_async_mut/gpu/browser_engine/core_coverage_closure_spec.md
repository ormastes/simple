# HTML Layout Renderer Core — :root Custom-Property Closure (U4.4, part N+2)

> This session builds the `HNode`/`SelectorContext`/`Rules` fixtures the prior

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 60 | 60 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# HTML Layout Renderer Core — :root Custom-Property Closure (U4.4, part N+2)

This session builds the `HNode`/`SelectorContext`/`Rules` fixtures the prior

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/gc_async_mut/gpu/browser_engine/core_coverage_closure_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Extension (session N+4) — the remaining four fixture-gated functions

This session builds the `HNode`/`SelectorContext`/`Rules` fixtures the prior
session deferred, closing `_pseudo_ctx_matches`,
`_extract_css_vw_with_rule_limit`, `_css_scan_rules_simple`, and
`compute_styles_with_material` (partially — it is a 465-line cascade
function; the new tests exercise the material-provenance branches and the
main per-node cascade entry, not every internal helper it calls).

`_extract_css_vw_with_rule_limit` and `_css_scan_rules_simple` turned out NOT
to need node fixtures at all — both operate purely on `html`/`css` text and
an `i32` limit, so they are exercised directly with crafted HTML/CSS strings
(traced against lines 431-445 for `@media` min-width/max-width semantics,
228-270 of `style/supports.spl` for a definite-true/definite-false
`@supports` query, and the brace-density guard at line ~482-493 for the
hostile-input truncation path).

`_pseudo_ctx_matches` needs a real `[HNode]` + `SelectorContext`: built here
with `mk_node`/`build_child_index`/`build_selector_context` from
`simple_web_html_layout_renderer_foundation.spl` (the same constructors the
existing `paint_primitives_coverage_closure_spec.spl` and
`containment_layout_contain_wired_spec.spl` specs use), forming a 4-node tree
`root -> {a, b}`, `a -> {c}`. Every pseudo-class branch's expected boolean is
hand-traced against `_child_position`/`_sibling_count`/`_node_is_empty`/
`_nth_child_matches`/`_has_option_matches` (lines 1166-1253) given that shape.

`compute_styles_with_material` is exercised through the same
`parse_html -> extract_css_vw -> build_child_index -> compute_styles_with_material`
pipeline the production caller uses (`simple_web_html_layout_renderer.spl`
lines 1796-1809), reusing the `data-wm-theme-*` fixture shape from
`simple_web_material_witness_spec.spl`'s `_cpu_material_node`/
`_solid_material_node` helpers. Expected admission outcomes are hand-traced
against the `cpu_admitted`/`solid_admitted` boolean expressions at lines
2925-2950.

## Scenarios

### core.spl: _css_collect_custom_props

#### returns empty when the stylesheet has no :root block

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- returns empty when the stylesheet has no :root block


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns empty when the stylesheet has no :root block")
val out = _css_collect_custom_props("body { color: red; }", "")
assert_equal(out, "")
```

</details>

#### collects a single base :root custom property

- collects a single base :root custom property


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("collects a single base :root custom property")
val out = _css_collect_custom_props(":root { --a: 1; }", "")
assert_equal(out, "--a:1\n")
```

</details>

#### collects multiple base :root custom properties in source order

- collects multiple base :root custom properties in source order


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("collects multiple base :root custom properties in source order")
val out = _css_collect_custom_props(
    ":root { --a: 1; --b: two; }", ""
)
assert_equal(out, "--a:1\n--b:two\n")
```

</details>

#### appends a matching :root[attr] variant after the base entries

- appends a matching :root[attr] variant after the base entries


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("appends a matching :root[attr] variant after the base entries")
val css = ":root { --a: 1; } :root[data-theme=\"dark\"] { --a: 2; }"
val out = _css_collect_custom_props(css, "data-theme=\"dark\"")
assert_equal(out, "--a:1\n--a:2\n")
```

</details>

#### skips a :root[attr] variant whose attribute does not match

- skips a :root[attr] variant whose attribute does not match


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("skips a :root[attr] variant whose attribute does not match")
val css = ":root { --a: 1; } :root[data-theme=\"dark\"] { --a: 2; }"
val out = _css_collect_custom_props(css, "data-theme=\"light\"")
assert_equal(out, "--a:1\n")
```

</details>

#### skips :root used as part of a larger compound selector

- skips :root used as part of a larger compound selector


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("skips :root used as part of a larger compound selector")
val out = _css_collect_custom_props(":root.dark { --a: 1; }", "")
assert_equal(out, "")
```

</details>

#### ignores declarations that are not custom properties (no -- prefix)

- ignores declarations that are not custom properties (no -- prefix)


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("ignores declarations that are not custom properties (no -- prefix)")
val out = _css_collect_custom_props(
    ":root { color: red; --a: 1; }", ""
)
assert_equal(out, "--a:1\n")
```

</details>

#### trims whitespace around the property name and value

- trims whitespace around the property name and value


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("trims whitespace around the property name and value")
val out = _css_collect_custom_props(
    ":root {   --a  :   1px  ; }", ""
)
assert_equal(out, "--a:1px\n")
```

</details>

### core.spl: _css_resolve_vars

#### returns the input unchanged when it contains no var()

- returns the input unchanged when it contains no var()


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns the input unchanged when it contains no var()")
val state = CssVarResolutionState.new("")
val result = _css_resolve_vars("solid red", state, 0, 0, false)
match result:
    CssVarResolution.Resolved(value):
        assert_equal(value, "solid red")
    _:
        assert_true(false)
```

</details>

#### reports DepthExceeded when resolution_depth exceeds the 32 cap

- reports DepthExceeded when resolution_depth exceeds the 32 cap


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("reports DepthExceeded when resolution_depth exceeds the 32 cap")
val state = CssVarResolutionState.new("--a:red")
val result = _css_resolve_vars("var(--a)", state, 33, 0, false)
match result:
    CssVarResolution.DepthExceeded:
        assert_true(true)
    _:
        assert_true(false)
```

</details>

#### reports BudgetExceeded when the substitution budget is exhausted

- reports BudgetExceeded when the substitution budget is exhausted


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("reports BudgetExceeded when the substitution budget is exhausted")
val state = CssVarResolutionState.new("--a:red")
state.remaining = 0
val result = _css_resolve_vars("var(--a)", state, 0, 0, false)
match result:
    CssVarResolution.BudgetExceeded:
        assert_true(true)
    _:
        assert_true(false)
```

</details>

#### substitutes a defined custom property with its value

- substitutes a defined custom property with its value


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("substitutes a defined custom property with its value")
val state = CssVarResolutionState.new("--a:red")
val result = _css_resolve_vars("var(--a)", state, 0, 0, false)
match result:
    CssVarResolution.Resolved(value):
        assert_equal(value, "red")
    _:
        assert_true(false)
```

</details>

#### keeps surrounding text around a substituted var()

- keeps surrounding text around a substituted var()


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("keeps surrounding text around a substituted var()")
val state = CssVarResolutionState.new("--a:red")
val result = _css_resolve_vars("solid var(--a) 1px", state, 0, 0, false)
match result:
    CssVarResolution.Resolved(value):
        assert_equal(value, "solid red 1px")
    _:
        assert_true(false)
```

</details>

#### falls back to the fallback text when the property is undefined

- falls back to the fallback text when the property is undefined


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("falls back to the fallback text when the property is undefined")
val state = CssVarResolutionState.new("")
val result = _css_resolve_vars(
    "var(--missing, blue)", state, 0, 0, false
)
match result:
    CssVarResolution.Resolved(value):
        assert_equal(value, "blue")
    _:
        assert_true(false)
```

</details>

#### preserves the var() source text for an undefined property with no fallback

- preserves the var() source text for an undefined property with no fallback


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("preserves the var() source text for an undefined property with no fallback")
val state = CssVarResolutionState.new("")
val result = _css_resolve_vars("var(--missing)", state, 0, 0, false)
match result:
    CssVarResolution.Resolved(value):
        assert_equal(value, "var(--missing)")
    _:
        assert_true(false)
```

</details>

#### resolves multiple var() occurrences in one declaration

- resolves multiple var() occurrences in one declaration


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("resolves multiple var() occurrences in one declaration")
val state = CssVarResolutionState.new("--a:1px\n--b:solid")
val result = _css_resolve_vars(
    "var(--a) var(--b)", state, 0, 0, false
)
match result:
    CssVarResolution.Resolved(value):
        assert_equal(value, "1px solid")
    _:
        assert_true(false)
```

</details>

### core.spl: _extract_css_vw_with_rule_limit

#### returns an empty Rules when requested_rule_limit is 0 or negative

- returns an empty Rules when requested_rule_limit is 0 or negative


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns an empty Rules when requested_rule_limit is 0 or negative")
val out = _extract_css_vw_with_rule_limit(
    "<html><style>div{color:red}</style></html>", 400, false, -1
)
assert_equal(out.group_parts.len(), 0)
assert_equal(out.decls.len(), 0)
```

</details>

#### collects a single style rule from one <style> block

- collects a single style rule from one <style> block


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("collects a single style rule from one <style> block")
val out = _extract_css_vw_with_rule_limit(
    "<html><style>div{color:red}</style></html>", 400, false, 10
)
assert_equal(out.group_parts.len(), 1)
assert_equal(out.decls[0], "color:red;")
```

</details>

#### strips a <template>'s <style> so it contributes no rule, keeping the sibling <style>

- strips a <template>'s <style> so it contributes no rule, keeping the sibling <style>


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("strips a <template>'s <style> so it contributes no rule, keeping the sibling <style>")
val html = (
    "<html><template><style>div{color:red}</style></template>" +
    "<style>span{color:blue}</style></html>"
)
val out = _extract_css_vw_with_rule_limit(html, 400, false, 10)
assert_equal(out.group_parts.len(), 1)
assert_equal(out.decls[0], "color:blue;")
```

</details>

#### includes an @media rule whose min-width condition is satisfied by the viewport

- includes an @media rule whose min-width condition is satisfied by the viewport


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("includes an @media rule whose min-width condition is satisfied by the viewport")
val html = (
    "<html><style>@media (min-width: 300px) {" +
    "div{color:red}}</style></html>"
)
val out = _extract_css_vw_with_rule_limit(html, 400, false, 10)
assert_equal(out.group_parts.len(), 1)
```

</details>

#### excludes an @media rule whose min-width condition is NOT satisfied by the viewport

- excludes an @media rule whose min-width condition is NOT satisfied by the viewport


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("excludes an @media rule whose min-width condition is NOT satisfied by the viewport")
val html = (
    "<html><style>@media (min-width: 300px) {" +
    "div{color:red}}</style></html>"
)
val out = _extract_css_vw_with_rule_limit(html, 100, false, 10)
assert_equal(out.group_parts.len(), 0)
```

</details>

#### includes an @supports rule whose query is definitely supported

- includes an @supports rule whose query is definitely supported


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("includes an @supports rule whose query is definitely supported")
val html = (
    "<html><style>@supports (display: block) {" +
    "div{color:red}}</style></html>"
)
val out = _extract_css_vw_with_rule_limit(html, 400, false, 10)
assert_equal(out.group_parts.len(), 1)
```

</details>

#### excludes an @supports rule whose query names an unknown property

- excludes an @supports rule whose query names an unknown property


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("excludes an @supports rule whose query names an unknown property")
val html = (
    "<html><style>@supports (not-a-real-prop: bar) {" +
    "div{color:red}}</style></html>"
)
val out = _extract_css_vw_with_rule_limit(html, 400, false, 10)
assert_equal(out.group_parts.len(), 0)
```

</details>

#### includes an @layer rule unconditionally

- includes an @layer rule unconditionally


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("includes an @layer rule unconditionally")
val html = (
    "<html><style>@layer base {" +
    "div{color:red}}</style></html>"
)
val out = _extract_css_vw_with_rule_limit(html, 400, false, 10)
assert_equal(out.group_parts.len(), 1)
```

</details>

### core.spl: _css_scan_rules_simple

#### returns an empty scan when requested_rule_cap is 0 or negative

- returns an empty scan when requested_rule_cap is 0 or negative


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns an empty scan when requested_rule_cap is 0 or negative")
val out = _css_scan_rules_simple("div{color:red}", -5)
assert_equal(out.selectors.len(), 0)
assert_equal(out.declarations.len(), 0)
```

</details>

#### returns an empty scan when the css has no opening brace at all

- returns an empty scan when the css has no opening brace at all


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns an empty scan when the css has no opening brace at all")
val out = _css_scan_rules_simple("div color red no braces here", 10)
assert_equal(out.selectors.len(), 0)
```

</details>

#### scans a plain rule with no @-wrapper (wrapper_counts stays 0)

- scans a plain rule with no @-wrapper (wrapper_counts stays 0)


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("scans a plain rule with no @-wrapper (wrapper_counts stays 0)")
val out = _css_scan_rules_simple("div{color:red}", 10)
assert_equal(out.selectors.len(), 1)
assert_equal(out.selectors[0], "div")
assert_equal(out.declarations[0], "color:red")
assert_equal(out.wrapper_counts[0], 0)
```

</details>

#### records a Media wrapper kind for a rule nested inside @media

- records a Media wrapper kind for a rule nested inside @media


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("records a Media wrapper kind for a rule nested inside @media")
val out = _css_scan_rules_simple(
    "@media (min-width:300px){div{color:red}}", 10
)
assert_equal(out.selectors.len(), 1)
assert_equal(out.wrapper_counts[0], 1)
match out.wrapper_kinds[0]:
    CssWrapperKind.Media:
        assert_true(true)
    _:
        assert_true(false)
```

</details>

#### records a Supports wrapper kind for a rule nested inside @supports

- records a Supports wrapper kind for a rule nested inside @supports


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("records a Supports wrapper kind for a rule nested inside @supports")
val out = _css_scan_rules_simple(
    "@supports (display:block){div{color:red}}", 10
)
assert_equal(out.wrapper_counts[0], 1)
match out.wrapper_kinds[0]:
    CssWrapperKind.Supports:
        assert_true(true)
    _:
        assert_true(false)
```

</details>

#### records a Layer wrapper kind for a rule nested inside @layer

- records a Layer wrapper kind for a rule nested inside @layer


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("records a Layer wrapper kind for a rule nested inside @layer")
val out = _css_scan_rules_simple(
    "@layer base{div{color:red}}", 10
)
assert_equal(out.wrapper_counts[0], 1)
match out.wrapper_kinds[0]:
    CssWrapperKind.Layer:
        assert_true(true)
    _:
        assert_true(false)
```

</details>

#### records an Unsupported wrapper kind for a rule nested inside an unrecognized at-rule

- records an Unsupported wrapper kind for a rule nested inside an unrecognized at-rule


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("records an Unsupported wrapper kind for a rule nested inside an unrecognized at-rule")
val out = _css_scan_rules_simple(
    "@foo bar{div{color:red}}", 10
)
assert_equal(out.wrapper_counts[0], 1)
match out.wrapper_kinds[0]:
    CssWrapperKind.Unsupported:
        assert_true(true)
    _:
        assert_true(false)
```

</details>

#### truncates hostile brace-dense input past the structural cap without emitting a rule

- truncates hostile brace-dense input past the structural cap without emitting a rule


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("truncates hostile brace-dense input past the structural cap without emitting a rule")
# rule_cap=1 -> structural_cap = 1*2+64 = 66. 100 "{" characters with
# no matching selector/declaration text trips excessive_structure
# (open-brace count 100 > 66), so bounded_css is cut to a 66-byte
# prefix of bare "{" characters -- no real selector ever forms, so
# zero rules are emitted, and the call must not crash.
var braces = ""
var n = 0
while n < 100:
    braces = braces + "{"
    n = n + 1
val out = _css_scan_rules_simple(braces, 1)
assert_equal(out.selectors.len(), 0)
```

</details>

### core.spl: _pseudo_ctx_matches

#### returns true immediately when the selector has no ':' pseudo-class at all

- returns true immediately when the selector has no ':' pseudo-class at all


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns true immediately when the selector has no ':' pseudo-class at all")
var root = mk_node("#root", -1)
var a = mk_node("div", 0)
var b = mk_node("div", 0)
var c = mk_node("div", 1)
val nodes = [root, a, b, c]
val child_index = build_child_index(nodes)
val ctx = build_selector_context(nodes, child_index)
assert_true(_pseudo_ctx_matches("div", nodes, ctx, 1))
```

</details>

#### ':empty' is true for a childless node and false for a node with a child

- ':empty' is true for a childless node and false for a node with a child


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("':empty' is true for a childless node and false for a node with a child")
var root = mk_node("#root", -1)
var a = mk_node("div", 0)
var b = mk_node("div", 0)
var c = mk_node("div", 1)
val nodes = [root, a, b, c]
val child_index = build_child_index(nodes)
val ctx = build_selector_context(nodes, child_index)
assert_true(_pseudo_ctx_matches("div:empty", nodes, ctx, 2))
assert_false(_pseudo_ctx_matches("div:empty", nodes, ctx, 1))
```

</details>

#### ':first-child' and ':last-child' match the correct sibling positions

- ':first-child' and ':last-child' match the correct sibling positions


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("':first-child' and ':last-child' match the correct sibling positions")
var root = mk_node("#root", -1)
var a = mk_node("div", 0)
var b = mk_node("div", 0)
var c = mk_node("div", 1)
val nodes = [root, a, b, c]
val child_index = build_child_index(nodes)
val ctx = build_selector_context(nodes, child_index)
assert_true(_pseudo_ctx_matches("div:first-child", nodes, ctx, 1))
assert_false(_pseudo_ctx_matches("div:first-child", nodes, ctx, 2))
assert_true(_pseudo_ctx_matches("div:last-child", nodes, ctx, 2))
assert_false(_pseudo_ctx_matches("div:last-child", nodes, ctx, 1))
```

</details>

#### ':only-child' is true only for a node whose parent has exactly one element child

- ':only-child' is true only for a node whose parent has exactly one element child


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("':only-child' is true only for a node whose parent has exactly one element child")
var root = mk_node("#root", -1)
var a = mk_node("div", 0)
var b = mk_node("div", 0)
var c = mk_node("div", 1)
val nodes = [root, a, b, c]
val child_index = build_child_index(nodes)
val ctx = build_selector_context(nodes, child_index)
assert_true(_pseudo_ctx_matches("div:only-child", nodes, ctx, 3))
assert_false(_pseudo_ctx_matches("div:only-child", nodes, ctx, 1))
```

</details>

#### ':nth-child(2)' matches only the second element child

- ':nth-child(2)' matches only the second element child


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("':nth-child(2)' matches only the second element child")
var root = mk_node("#root", -1)
var a = mk_node("div", 0)
var b = mk_node("div", 0)
var c = mk_node("div", 1)
val nodes = [root, a, b, c]
val child_index = build_child_index(nodes)
val ctx = build_selector_context(nodes, child_index)
assert_true(_pseudo_ctx_matches("div:nth-child(2)", nodes, ctx, 2))
assert_false(_pseudo_ctx_matches("div:nth-child(2)", nodes, ctx, 1))
```

</details>

#### already-handled state/list pseudos (:hover, :root, :not()) pass through as true

- already-handled state/list pseudos (:hover, :root, :not()) pass through as true


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("already-handled state/list pseudos (:hover, :root, :not()) pass through as true")
var root = mk_node("#root", -1)
var a = mk_node("div", 0)
var b = mk_node("div", 0)
var c = mk_node("div", 1)
val nodes = [root, a, b, c]
val child_index = build_child_index(nodes)
val ctx = build_selector_context(nodes, child_index)
assert_true(_pseudo_ctx_matches("div:hover", nodes, ctx, 1))
assert_true(_pseudo_ctx_matches("div:not(.x)", nodes, ctx, 1))
assert_true(_pseudo_ctx_matches("html:root", nodes, ctx, 0))
```

</details>

#### ':root[attr]' skips the bracketed attribute suffix before falling through to the already-checked branch

- ':root[attr]' skips the bracketed attribute suffix before falling through to the already-checked branch


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("':root[attr]' skips the bracketed attribute suffix before falling through to the already-checked branch")
var root = mk_node("#root", -1)
var a = mk_node("div", 0)
var b = mk_node("div", 0)
var c = mk_node("div", 1)
val nodes = [root, a, b, c]
val child_index = build_child_index(nodes)
val ctx = build_selector_context(nodes, child_index)
assert_true(_pseudo_ctx_matches("html:root[data-theme]", nodes, ctx, 0))
```

</details>

#### an unrecognized pseudo-class name returns false

- an unrecognized pseudo-class name returns false


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("an unrecognized pseudo-class name returns false")
var root = mk_node("#root", -1)
var a = mk_node("div", 0)
var b = mk_node("div", 0)
var c = mk_node("div", 1)
val nodes = [root, a, b, c]
val child_index = build_child_index(nodes)
val ctx = build_selector_context(nodes, child_index)
assert_false(_pseudo_ctx_matches("div:unknownpseudo", nodes, ctx, 1))
```

</details>

#### an unclosed functional pseudo-class argument returns false

- an unclosed functional pseudo-class argument returns false


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("an unclosed functional pseudo-class argument returns false")
var root = mk_node("#root", -1)
var a = mk_node("div", 0)
var b = mk_node("div", 0)
var c = mk_node("div", 1)
val nodes = [root, a, b, c]
val child_index = build_child_index(nodes)
val ctx = build_selector_context(nodes, child_index)
assert_false(_pseudo_ctx_matches("div:nth-child(2", nodes, ctx, 1))
```

</details>

#### ':has(div)' is true when a descendant matches and false when none does

- ':has(div)' is true when a descendant matches and false when none does


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("':has(div)' is true when a descendant matches and false when none does")
var root = mk_node("#root", -1)
var a = mk_node("div", 0)
var b = mk_node("div", 0)
var c = mk_node("div", 1)
val nodes = [root, a, b, c]
val child_index = build_child_index(nodes)
val ctx = build_selector_context(nodes, child_index)
assert_true(_pseudo_ctx_matches("div:has(div)", nodes, ctx, 0))
assert_false(_pseudo_ctx_matches("div:has(span)", nodes, ctx, 0))
```

</details>

#### ':has(span, div)' matches on the second comma-separated option

- ':has(span, div)' matches on the second comma-separated option


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("':has(span, div)' matches on the second comma-separated option")
var root = mk_node("#root", -1)
var a = mk_node("div", 0)
var b = mk_node("div", 0)
var c = mk_node("div", 1)
val nodes = [root, a, b, c]
val child_index = build_child_index(nodes)
val ctx = build_selector_context(nodes, child_index)
assert_true(_pseudo_ctx_matches("div:has(span, div)", nodes, ctx, 0))
```

</details>

### core.spl: compute_styles_with_material

#### admits a CPU-composited material entry for a node meeting every admission condition

- admits a CPU-composited material entry for a node meeting every admission condition


<details>
<summary>Executable SSpec</summary>

Runnable source: 27 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("admits a CPU-composited material entry for a node meeting every admission condition")
val html = (
    "<html><body><section id='s' " +
    "data-wm-theme-material-mode='engine2d-cpu-composited-material-v1' " +
    "data-wm-theme-fallback='solid-material' " +
    "data-wm-theme-bg='#123456' " +
    "style='background:rgba(31,31,33,0.80);" +
    "backdrop-filter:blur(4px) saturate(120%)'>" +
    "</section></body></html>"
)
val nodes = parse_html(html)
val rules = extract_css_vw(html, 400, false)
val child_index = build_child_index(nodes)
var material_entries: [text] = ["", ""]
var material_counts: [i64] = [0, 0]
var cpu_material_nodes: [i32] = []
var solid_material_nodes: [i32] = []
val styles = compute_styles_with_material(
    nodes, rules, child_index, false, true,
    material_entries, material_counts,
    cpu_material_nodes, solid_material_nodes
)
assert_equal(styles.len(), nodes.len())
assert_equal(material_counts[0], 1)
assert_equal(cpu_material_nodes.len(), 1)
assert_equal(material_counts[1], 0)
```

</details>

#### admits a solid-material entry for an opaque node with no backdrop/gradient/mode

- admits a solid-material entry for an opaque node with no backdrop/gradient/mode


<details>
<summary>Executable SSpec</summary>

Runnable source: 24 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("admits a solid-material entry for an opaque node with no backdrop/gradient/mode")
val html = (
    "<html><body><section id='s' " +
    "data-wm-theme-fallback='solid-material' " +
    "data-wm-theme-bg='#123456' " +
    "style='background:#123456'>" +
    "</section></body></html>"
)
val nodes = parse_html(html)
val rules = extract_css_vw(html, 400, false)
val child_index = build_child_index(nodes)
var material_entries: [text] = ["", ""]
var material_counts: [i64] = [0, 0]
var cpu_material_nodes: [i32] = []
var solid_material_nodes: [i32] = []
val styles = compute_styles_with_material(
    nodes, rules, child_index, false, true,
    material_entries, material_counts,
    cpu_material_nodes, solid_material_nodes
)
assert_equal(material_counts[1], 1)
assert_equal(solid_material_nodes.len(), 1)
assert_equal(material_counts[0], 0)
```

</details>

#### admits neither material channel for a plain node with no data-wm-theme-fallback contract

- admits neither material channel for a plain node with no data-wm-theme-fallback contract


<details>
<summary>Executable SSpec</summary>

Runnable source: 22 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("admits neither material channel for a plain node with no data-wm-theme-fallback contract")
val html = (
    "<html><body><div id='plain' style='color:red'>" +
    "hello</div></body></html>"
)
val nodes = parse_html(html)
val rules = extract_css_vw(html, 400, false)
val child_index = build_child_index(nodes)
var material_entries: [text] = ["", ""]
var material_counts: [i64] = [0, 0]
var cpu_material_nodes: [i32] = []
var solid_material_nodes: [i32] = []
val styles = compute_styles_with_material(
    nodes, rules, child_index, false, true,
    material_entries, material_counts,
    cpu_material_nodes, solid_material_nodes
)
assert_equal(material_counts[0], 0)
assert_equal(material_counts[1], 0)
assert_equal(cpu_material_nodes.len(), 0)
assert_equal(solid_material_nodes.len(), 0)
```

</details>

#### applies an id-selector CSS rule's cascade onto the matching node's computed style

- applies an id-selector CSS rule's cascade onto the matching node's computed style


<details>
<summary>Executable SSpec</summary>

Runnable source: 19 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("applies an id-selector CSS rule's cascade onto the matching node's computed style")
val html = (
    "<html><style>#target{color:red}</style>" +
    "<body><div id='target'>hi</div></body></html>"
)
val nodes = parse_html(html)
val rules = extract_css_vw(html, 400, false)
val child_index = build_child_index(nodes)
var material_entries: [text] = ["", ""]
var material_counts: [i64] = [0, 0]
var cpu_material_nodes: [i32] = []
var solid_material_nodes: [i32] = []
val styles = compute_styles_with_material(
    nodes, rules, child_index, false, true,
    material_entries, material_counts,
    cpu_material_nodes, solid_material_nodes
)
assert_equal(styles.len(), nodes.len())
```

</details>

### core.spl: _css_resolve_vars — cycle detection

#### a direct self-reference with no fallback keeps its var() source text

- a direct self-reference with no fallback keeps its var() source text


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("a direct self-reference with no fallback keeps its var() source text")
val state = CssVarResolutionState.new("--a:var(--a)")
val result = _css_resolve_vars("var(--a)", state, 0, 0, false)
match result:
    CssVarResolution.Resolved(value):
        assert_equal(value, "var(--a)")
    _:
        assert_true(false)
```

</details>

#### a direct self-reference WITH a fallback resolves to the fallback text

- a direct self-reference WITH a fallback resolves to the fallback text


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("a direct self-reference WITH a fallback resolves to the fallback text")
val state = CssVarResolutionState.new("--a:var(--a)")
val result = _css_resolve_vars("var(--a, blue)", state, 0, 0, false)
match result:
    CssVarResolution.Resolved(value):
        assert_equal(value, "blue")
    _:
        assert_true(false)
```

</details>

#### reports DepthExceeded via the active-names capacity guard, independent of resolution_depth

- reports DepthExceeded via the active-names capacity guard, independent of resolution_depth


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("reports DepthExceeded via the active-names capacity guard, independent of resolution_depth")
val state = CssVarResolutionState.new("--a:red")
val result = _css_resolve_vars("var(--a)", state, 0, 33, false)
match result:
    CssVarResolution.DepthExceeded:
        assert_true(true)
    _:
        assert_true(false)
```

</details>

### core.spl: _css_scan_rules_simple — wrapper overflow

#### pushes a synthetic Unsupported/@unsupported-overflow wrapper past 32 nested @-wrappers

- pushes a synthetic Unsupported/@unsupported-overflow wrapper past 32 nested @-wrappers


<details>
<summary>Executable SSpec</summary>

Runnable source: 22 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("pushes a synthetic Unsupported/@unsupported-overflow wrapper past 32 nested @-wrappers")
var css = ""
var depth_i = 0
while depth_i < 34:
    css = css + "@layer l" + depth_i.to_text() + "{"
    depth_i = depth_i + 1
css = css + "div{color:red}"
var close_i = 0
while close_i < 34:
    css = css + "}"
    close_i = close_i + 1
val out = _css_scan_rules_simple(css, 10)
assert_equal(out.selectors.len(), 1)
val last_kind_idx = out.wrapper_kinds.len() - 1
val last_prelude_idx = out.wrapper_preludes.len() - 1
match out.wrapper_kinds[last_kind_idx]:
    CssWrapperKind.Unsupported:
        assert_true(true)
    _:
        assert_true(false)
assert_equal(out.wrapper_preludes[last_prelude_idx], "@unsupported-overflow")
```

</details>

### core.spl: _extract_css_vw_with_rule_limit — media-group shapes

#### includes an @media rule whose max-width condition is satisfied by the viewport

- includes an @media rule whose max-width condition is satisfied by the viewport


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("includes an @media rule whose max-width condition is satisfied by the viewport")
val html = (
    "<html><style>@media (max-width: 500px) {" +
    "div{color:red}}</style></html>"
)
val out = _extract_css_vw_with_rule_limit(html, 400, false, 10)
assert_equal(out.group_parts.len(), 1)
```

</details>

#### excludes an @media rule whose max-width condition is NOT satisfied by the viewport

- excludes an @media rule whose max-width condition is NOT satisfied by the viewport


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("excludes an @media rule whose max-width condition is NOT satisfied by the viewport")
val html = (
    "<html><style>@media (max-width: 500px) {" +
    "div{color:red}}</style></html>"
)
val out = _extract_css_vw_with_rule_limit(html, 600, false, 10)
assert_equal(out.group_parts.len(), 0)
```

</details>

#### excludes an @media rule whose feature name is unrecognized (neither min-width nor max-width)

- excludes an @media rule whose feature name is unrecognized (neither min-width nor max-width)


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("excludes an @media rule whose feature name is unrecognized (neither min-width nor max-width)")
val html = (
    "<html><style>@media (prefers-color-scheme: dark) {" +
    "div{color:red}}</style></html>"
)
val out = _extract_css_vw_with_rule_limit(html, 400, false, 10)
assert_equal(out.group_parts.len(), 0)
```

</details>

#### includes an @media rule via its second comma-separated group when the first group fails

- includes an @media rule via its second comma-separated group when the first group fails


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("includes an @media rule via its second comma-separated group when the first group fails")
val html = (
    "<html><style>@media (min-width: 999px), (max-width: 999px) {" +
    "div{color:red}}</style></html>"
)
val out = _extract_css_vw_with_rule_limit(html, 400, false, 10)
assert_equal(out.group_parts.len(), 1)
```

</details>

### core.spl: compute_styles_with_material — rejection diagnostic

#### reaches the entry-rejected diagnostic when the fallback contract is declared but no admission condition is met

- reaches the entry-rejected diagnostic when the fallback contract is declared but no admission condition is met


<details>
<summary>Executable SSpec</summary>

Runnable source: 24 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("reaches the entry-rejected diagnostic when the fallback contract is declared but no admission condition is met")
val html = (
    "<html><body><section id='s' " +
    "data-wm-theme-fallback='solid-material' " +
    "style='background:#123456'>" +
    "</section></body></html>"
)
val nodes = parse_html(html)
val rules = extract_css_vw(html, 400, false)
val child_index = build_child_index(nodes)
var material_entries: [text] = ["", ""]
var material_counts: [i64] = [0, 0]
var cpu_material_nodes: [i32] = []
var solid_material_nodes: [i32] = []
val styles = compute_styles_with_material(
    nodes, rules, child_index, false, true,
    material_entries, material_counts,
    cpu_material_nodes, solid_material_nodes
)
assert_equal(material_counts[0], 0)
assert_equal(material_counts[1], 0)
assert_equal(cpu_material_nodes.len(), 0)
assert_equal(solid_material_nodes.len(), 0)
```

</details>

### core.spl: compute_styles_with_material — material_channel_ready false

#### skips both material channels and the trailing count-write when the material arrays are too short

- skips both material channels and the trailing count-write when the material arrays are too short


<details>
<summary>Executable SSpec</summary>

Runnable source: 28 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("skips both material channels and the trailing count-write when the material arrays are too short")
val html = (
    "<html><body><section id='s' " +
    "data-wm-theme-material-mode='engine2d-cpu-composited-material-v1' " +
    "data-wm-theme-fallback='solid-material' " +
    "data-wm-theme-bg='#123456' " +
    "style='background:rgba(31,31,33,0.80);" +
    "backdrop-filter:blur(4px) saturate(120%)'>" +
    "</section></body></html>"
)
val nodes = parse_html(html)
val rules = extract_css_vw(html, 400, false)
val child_index = build_child_index(nodes)
var material_entries: [text] = []
var material_counts: [i64] = []
var cpu_material_nodes: [i32] = []
var solid_material_nodes: [i32] = []
val styles = compute_styles_with_material(
    nodes, rules, child_index, false, true,
    material_entries, material_counts,
    cpu_material_nodes, solid_material_nodes
)
assert_equal(styles.len(), nodes.len())
assert_equal(material_entries.len(), 0)
assert_equal(material_counts.len(), 0)
assert_equal(cpu_material_nodes.len(), 0)
assert_equal(solid_material_nodes.len(), 0)
```

</details>

### core.spl: compute_styles_with_material — trace_stages=true

#### runs the full [layout-trace] print family without crashing and still computes styles

- runs the full [layout-trace] print family without crashing and still computes styles


<details>
<summary>Executable SSpec</summary>

Runnable source: 19 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("runs the full [layout-trace] print family without crashing and still computes styles")
val html = (
    "<html><style>#target{color:red}</style>" +
    "<body><div id='target'>hi</div></body></html>"
)
val nodes = parse_html(html)
val rules = extract_css_vw(html, 400, false)
val child_index = build_child_index(nodes)
var material_entries: [text] = ["", ""]
var material_counts: [i64] = [0, 0]
var cpu_material_nodes: [i32] = []
var solid_material_nodes: [i32] = []
val styles = compute_styles_with_material(
    nodes, rules, child_index, true, true,
    material_entries, material_counts,
    cpu_material_nodes, solid_material_nodes
)
assert_equal(styles.len(), nodes.len())
```

</details>

### core.spl: compute_styles_with_material — empty-cells:hide

#### blanks the background of a content-empty td whose matched RULE sets empty-cells:hide

- blanks the background of a content-empty td whose matched RULE sets empty-cells:hide


<details>
<summary>Executable SSpec</summary>

Runnable source: 26 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("blanks the background of a content-empty td whose matched RULE sets empty-cells:hide")
val html = (
    "<html><style>td{empty-cells:hide}</style>" +
    "<body><table><tr><td id='c'></td></tr></table></body></html>"
)
val nodes = parse_html(html)
val rules = extract_css_vw(html, 400, false)
val child_index = build_child_index(nodes)
var material_entries: [text] = ["", ""]
var material_counts: [i64] = [0, 0]
var cpu_material_nodes: [i32] = []
var solid_material_nodes: [i32] = []
val styles = compute_styles_with_material(
    nodes, rules, child_index, false, true,
    material_entries, material_counts,
    cpu_material_nodes, solid_material_nodes
)
var idx = 0
var found = false
while idx < nodes.len():
    if nodes[idx].tag == "td":
        assert_equal(styles[idx].bg, 0u32)
        found = true
    idx = idx + 1
assert_true(found)
```

</details>

#### blanks the background of a content-empty td whose INLINE style sets empty-cells:hide

- blanks the background of a content-empty td whose INLINE style sets empty-cells:hide


<details>
<summary>Executable SSpec</summary>

Runnable source: 27 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("blanks the background of a content-empty td whose INLINE style sets empty-cells:hide")
val html = (
    "<html><body><table><tr>" +
    "<td id='c' style='empty-cells:hide'></td>" +
    "</tr></table></body></html>"
)
val nodes = parse_html(html)
val rules = extract_css_vw(html, 400, false)
val child_index = build_child_index(nodes)
var material_entries: [text] = ["", ""]
var material_counts: [i64] = [0, 0]
var cpu_material_nodes: [i32] = []
var solid_material_nodes: [i32] = []
val styles = compute_styles_with_material(
    nodes, rules, child_index, false, true,
    material_entries, material_counts,
    cpu_material_nodes, solid_material_nodes
)
var idx = 0
var found = false
while idx < nodes.len():
    if nodes[idx].tag == "td":
        assert_equal(styles[idx].bg, 0u32)
        found = true
    idx = idx + 1
assert_true(found)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 60 |
| Active scenarios | 60 |
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

- Canonical SPipe generation for source `3bbe36cc48b6d8f6f9c4684c895cf4cf2f99f6e9407ff35a9f01f50ceeb3a643`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `3bbe36cc48b6d8f6f9c4684c895cf4cf2f99f6e9407ff35a9f01f50ceeb3a643`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `3bbe36cc48b6d8f6f9c4684c895cf4cf2f99f6e9407ff35a9f01f50ceeb3a643`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/01_unit/lib/gc_async_mut/gpu/browser_engine/core_coverage_closure_spec.spl
mirror: doc/06_spec/01_unit/lib/gc_async_mut/gpu/browser_engine/core_coverage_closure_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/lib/gc_async_mut/gpu/browser_engine/core_coverage_closure_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/lib/gc_async_mut/gpu/browser_engine/core_coverage_closure_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/lib/gc_async_mut/gpu/browser_engine/core_coverage_closure_spec.spl:98:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'returns empty when the stylesheet has no :root block' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/gc_async_mut/gpu/browser_engine/core_coverage_closure_spec.spl:104:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'collects a single base :root custom property' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/gc_async_mut/gpu/browser_engine/core_coverage_closure_spec.spl:110:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'collects multiple base :root custom properties in source order' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
