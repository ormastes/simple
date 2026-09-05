# Browser Renderer Utils — Coverage Closure

> Purpose: Prove that search primitives (coverage closure).

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 22 | 22 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Browser Renderer Utils — Coverage Closure

Purpose: Prove that search primitives (coverage closure).

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/01_unit/browser_engine/browser_renderer_utils_coverage_closure_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Purpose and audience
Purpose: Prove that search primitives (coverage closure).
Audience: compiler and tooling engineers who maintain this spec.

## Scenarios

### search primitives (coverage closure)

#### finds a char at/after start and returns the sentinel when absent

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- finds a char at/after start and returns the sentinel when absent
- Verify: finds a char at/after start and returns the sentinel when absent
   - Expected: browser_renderer_find_char("a=b=c", "=", 0) equals `1`
   - Expected: browser_renderer_find_char("a=b=c", "=", 2) equals `3`
   - Expected: browser_renderer_find_char("abc", "z", 0) equals `999999999`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-BROWSER_ENGINE
step("finds a char at/after start and returns the sentinel when absent")
step("Verify: finds a char at/after start and returns the sentinel when absent")
# @req: REQ-BROWSER-ENGINE-BROWSER-RENDERER-UTILS-COVERAGE-CLOSURE-SPEC-SPL-001
expect(browser_renderer_find_char("a=b=c", "=", 0)).to_equal(1)
expect(browser_renderer_find_char("a=b=c", "=", 2)).to_equal(3)
expect(browser_renderer_find_char("abc", "z", 0)).to_equal(999999999)
```

</details>

#### finds a substring and returns the sentinel when absent

- finds a substring and returns the sentinel when absent
- Verify: finds a substring and returns the sentinel when absent
   - Expected: br_find_str("abcabc", "bc", 0) equals `1`
   - Expected: br_find_str("abcabc", "bc", 2) equals `4`
   - Expected: br_find_str("abcabc", "zz", 0) equals `999999999`
   - Expected: br_find_str("ababac", "abac", 0) equals `2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-BROWSER_ENGINE
step("finds a substring and returns the sentinel when absent")
step("Verify: finds a substring and returns the sentinel when absent")
expect(br_find_str("abcabc", "bc", 0)).to_equal(1)
expect(br_find_str("abcabc", "bc", 2)).to_equal(4)
expect(br_find_str("abcabc", "zz", 0)).to_equal(999999999)
expect(br_find_str("ababac", "abac", 0)).to_equal(2)
```

</details>

#### matches nested parens and braces, sentinel when unbalanced

- matches nested parens and braces, sentinel when unbalanced
- Verify: matches nested parens and braces, sentinel when unbalanced
   - Expected: br_find_matching_paren("f(a(b)c)d", 1) equals `7`
   - Expected: br_find_matching_paren("f(a(b", 1) equals `999999999`
   - Expected: br_find_matching_brace("a{b{c}d}e", 1) equals `7`
   - Expected: br_find_matching_brace("a{b{c", 1) equals `999999999`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-BROWSER_ENGINE
step("matches nested parens and braces, sentinel when unbalanced")
step("Verify: matches nested parens and braces, sentinel when unbalanced")
expect(br_find_matching_paren("f(a(b)c)d", 1)).to_equal(7)
expect(br_find_matching_paren("f(a(b", 1)).to_equal(999999999)
expect(br_find_matching_brace("a{b{c}d}e", 1)).to_equal(7)
expect(br_find_matching_brace("a{b{c", 1)).to_equal(999999999)
```

</details>

### splitters (coverage closure)

#### splits tag parts, keeping quoted whitespace inside one part

- splits tag parts, keeping quoted whitespace inside one part
- Verify: splits tag parts, keeping quoted whitespace inside one part
   - Expected: parts.len() equals `3`
   - Expected: parts[0] equals `div`
   - Expected: parts[1] equals `class="a b"`
   - Expected: parts[2] equals `id='x'`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-BROWSER_ENGINE
step("splits tag parts, keeping quoted whitespace inside one part")
step("Verify: splits tag parts, keeping quoted whitespace inside one part")
val parts = browser_renderer_split_tag_parts("div class=\"a b\" id='x'")
expect(parts.len()).to_equal(3)  # oracle: 3 — named expected value from the requirement
expect(parts[0]).to_equal("div")
expect(parts[1]).to_equal("class=\"a b\"")
expect(parts[2]).to_equal("id='x'")
```

</details>

#### splits on all whitespace kinds and handles empty input

- splits on all whitespace kinds and handles empty input
- Verify: splits on all whitespace kinds and handles empty input
   - Expected: parts.len() equals `4`
   - Expected: parts[0] equals `a`
   - Expected: parts[3] equals `d`
   - Expected: browser_renderer_split_spaces("").len() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-BROWSER_ENGINE
step("splits on all whitespace kinds and handles empty input")
step("Verify: splits on all whitespace kinds and handles empty input")
val parts = browser_renderer_split_spaces(" a\tb\nc\r d ")
expect(parts.len()).to_equal(4)  # oracle: 4 — named expected value from the requirement
expect(parts[0]).to_equal("a")
expect(parts[3]).to_equal("d")
expect(browser_renderer_split_spaces("").len()).to_equal(0)
```

</details>

#### splits semicolons, trimming and dropping empty segments

- splits semicolons, trimming and dropping empty segments
- Verify: splits semicolons, trimming and dropping empty segments
   - Expected: parts.len() equals `2`
   - Expected: parts[0] equals `color:red`
   - Expected: parts[1] equals `width:5px`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-BROWSER_ENGINE
step("splits semicolons, trimming and dropping empty segments")
step("Verify: splits semicolons, trimming and dropping empty segments")
val parts = browser_renderer_split_semicolons(" color:red ;; width:5px ")
expect(parts.len()).to_equal(2)  # oracle: 2 — named expected value from the requirement
expect(parts[0]).to_equal("color:red")
expect(parts[1]).to_equal("width:5px")
```

</details>

### tag helpers (coverage closure)

#### classifies void and non-void elements

- classifies void and non-void elements
- Verify: classifies void and non-void elements
   - Expected: browser_renderer_is_void_element("br") is true
   - Expected: browser_renderer_is_void_element("img") is true
   - Expected: browser_renderer_is_void_element("div") is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-BROWSER_ENGINE
step("classifies void and non-void elements")
step("Verify: classifies void and non-void elements")
expect(browser_renderer_is_void_element("br")).to_equal(true)
expect(browser_renderer_is_void_element("img")).to_equal(true)
expect(browser_renderer_is_void_element("div")).to_equal(false)
```

</details>

#### reads attribute values with double, single, and no quotes

- reads attribute values with double, single, and no quotes
- Verify: reads attribute values with double, single, and no quotes
   - Expected: br_tag_attr_value("a href=\"x\" id=y", "href") equals `x`
   - Expected: br_tag_attr_value("a href='x'", "href") equals `x`
   - Expected: br_tag_attr_value("a id=y", "id") equals `y`
   - Expected: br_tag_attr_value("a id=y", "href") equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-BROWSER_ENGINE
step("reads attribute values with double, single, and no quotes")
step("Verify: reads attribute values with double, single, and no quotes")
expect(br_tag_attr_value("a href=\"x\" id=y", "href")).to_equal("x")
expect(br_tag_attr_value("a href='x'", "href")).to_equal("x")
expect(br_tag_attr_value("a id=y", "id")).to_equal("y")
expect(br_tag_attr_value("a id=y", "href")).to_equal("")
```

</details>

#### detects bare and valued attributes

- detects bare and valued attributes
- Verify: detects bare and valued attributes
   - Expected: br_tag_has_attr("input disabled", "disabled") is true
   - Expected: br_tag_has_attr("input type=\"text\"", "type") is true
   - Expected: br_tag_has_attr("input type=\"text\"", "disabled") is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-BROWSER_ENGINE
step("detects bare and valued attributes")
step("Verify: detects bare and valued attributes")
expect(br_tag_has_attr("input disabled", "disabled")).to_equal(true)
expect(br_tag_has_attr("input type=\"text\"", "type")).to_equal(true)
expect(br_tag_has_attr("input type=\"text\"", "disabled")).to_equal(false)
```

</details>

#### unquotes only fully quoted values

- unquotes only fully quoted values
- Verify: unquotes only fully quoted values
   - Expected: br_unquote_attr_value("\"x\"") equals `x`
   - Expected: br_unquote_attr_value("'x'") equals `x`
   - Expected: br_unquote_attr_value("x") equals `x`
   - Expected: br_unquote_attr_value("'") equals `'`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-BROWSER_ENGINE
step("unquotes only fully quoted values")
step("Verify: unquotes only fully quoted values")
expect(br_unquote_attr_value("\"x\"")).to_equal("x")
expect(br_unquote_attr_value("'x'")).to_equal("x")
expect(br_unquote_attr_value("x")).to_equal("x")
expect(br_unquote_attr_value("'")).to_equal("'")
```

</details>

### style property helpers (coverage closure)

#### merges style text with empty-side short-circuits

- merges style text with empty-side short-circuits
- Verify: merges style text with empty-side short-circuits
   - Expected: br_merge_style_text("", "b:1") equals `b:1`
   - Expected: br_merge_style_text("a:1", "") equals `a:1`
   - Expected: br_merge_style_text("a:1", "b:2") equals `a:1;b:2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-BROWSER_ENGINE
step("merges style text with empty-side short-circuits")
step("Verify: merges style text with empty-side short-circuits")
expect(br_merge_style_text("", "b:1")).to_equal("b:1")
expect(br_merge_style_text("a:1", "")).to_equal("a:1")
expect(br_merge_style_text("a:1", "b:2")).to_equal("a:1;b:2")
```

</details>

#### returns the LAST declaration for a property, empty when absent

- returns the LAST declaration for a property, empty when absent
- Verify: returns the LAST declaration for a property, empty when absent
   - Expected: br_style_property_value("color:red;color:blue", "color") equals `blue`
   - Expected: br_style_property_value("color:red", "width") equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-BROWSER_ENGINE
step("returns the LAST declaration for a property, empty when absent")
step("Verify: returns the LAST declaration for a property, empty when absent")
expect(br_style_property_value("color:red;color:blue", "color")).to_equal("blue")
expect(br_style_property_value("color:red", "width")).to_equal("")
```

</details>

#### parses px values with fallback paths

- parses px values with fallback paths
- Verify: parses px values with fallback paths
   - Expected: br_parse_px_i32("12px", 0) equals `12`
   - Expected: br_parse_px_i32("-4px", 0) equals `-4`
   - Expected: br_parse_px_i32("12.7px", 0) equals `12`
   - Expected: br_parse_px_i32("auto", 7) equals `7`
   - Expected: br_parse_px_i32(".5", 7) equals `7`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-BROWSER_ENGINE
step("parses px values with fallback paths")
step("Verify: parses px values with fallback paths")
expect(br_parse_px_i32("12px", 0)).to_equal(12)
expect(br_parse_px_i32("-4px", 0)).to_equal(-4)
expect(br_parse_px_i32("12.7px", 0)).to_equal(12)
expect(br_parse_px_i32("auto", 7)).to_equal(7)
expect(br_parse_px_i32(".5", 7)).to_equal(7)
```

</details>

#### resolves style px with default fallback

- resolves style px with default fallback
- Verify: resolves style px with default fallback
   - Expected: br_style_px_or_default("width: 30px", "width", 5) equals `30`
   - Expected: br_style_px_or_default("width: 30px", "height", 5) equals `5`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-BROWSER_ENGINE
step("resolves style px with default fallback")
step("Verify: resolves style px with default fallback")
expect(br_style_px_or_default("width: 30px", "width", 5)).to_equal(30)
expect(br_style_px_or_default("width: 30px", "height", 5)).to_equal(5)
```

</details>

#### evaluates calc() addition, subtraction, plain, and malformed

- evaluates calc() addition, subtraction, plain, and malformed
- Verify: evaluates calc() addition, subtraction, plain, and malformed
   - Expected: br_parse_calc_px_i32("calc(10px + 5px)", 0) equals `15`
   - Expected: br_parse_calc_px_i32("calc(10px - 4px)", 0) equals `6`
   - Expected: br_parse_calc_px_i32("calc(9px)", 0) equals `9`
   - Expected: br_parse_calc_px_i32("calc(", 3) equals `3`
   - Expected: br_parse_calc_px_i32("calc(a + b)", 3) equals `3`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-BROWSER_ENGINE
step("evaluates calc() addition, subtraction, plain, and malformed")
step("Verify: evaluates calc() addition, subtraction, plain, and malformed")
expect(br_parse_calc_px_i32("calc(10px + 5px)", 0)).to_equal(15)
expect(br_parse_calc_px_i32("calc(10px - 4px)", 0)).to_equal(6)
expect(br_parse_calc_px_i32("calc(9px)", 0)).to_equal(9)
expect(br_parse_calc_px_i32("calc(", 3)).to_equal(3)
expect(br_parse_calc_px_i32("calc(a + b)", 3)).to_equal(3)
```

</details>

### CSS flatteners (coverage closure)

#### keeps a passing @supports body and drops a failing one

- keeps a passing @supports body and drops a failing one
- Verify: keeps a passing @supports body and drops a failing one
   - Expected: flat contains `rule`
   - Expected: bad does not contain `color: red`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-BROWSER_ENGINE
step("keeps a passing @supports body and drops a failing one")
step("Verify: keeps a passing @supports body and drops a failing one")
val ob = 123.chr()
val cb = 125.chr()
val rule = "a " + ob + " color: red " + cb
val css = "@supports (display: block) " + ob + " " + rule + " " + cb
val flat = br_flatten_supports_blocks(css)
expect(flat.contains(rule)).to_equal(true)
val bad = br_flatten_supports_blocks("@supports (frob: nope) " + ob + " " + rule + " " + cb)
expect(bad.contains("color: red")).to_equal(false)
```

</details>

#### passes css without @supports through unchanged

- passes css without @supports through unchanged
- Verify: passes css without @supports through unchanged
   - Expected: br_flatten_supports_blocks(css) equals `css`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-BROWSER_ENGINE
step("passes css without @supports through unchanged")
step("Verify: passes css without @supports through unchanged")
val css = "a " + 123.chr() + " x:1 " + 125.chr()
expect(br_flatten_supports_blocks(css)).to_equal(css)
```

</details>

#### unwraps @layer blocks and leaves plain rules alone

- unwraps @layer blocks and leaves plain rules alone
- Verify: unwraps @layer blocks and leaves plain rules alone
   - Expected: flat contains `inner`
   - Expected: flat does not contain `@layer`
   - Expected: flat contains `plain`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-BROWSER_ENGINE
step("unwraps @layer blocks and leaves plain rules alone")
step("Verify: unwraps @layer blocks and leaves plain rules alone")
val ob = 123.chr()
val cb = 125.chr()
val inner = "a " + ob + " color: red " + cb
val plain = "b " + ob + " x:1 " + cb
val flat = br_flatten_layer_blocks("@layer base " + ob + " " + inner + " " + cb + " " + plain)
expect(flat.contains(inner)).to_equal(true)
expect(flat.contains("@layer")).to_equal(false)
expect(flat.contains(plain)).to_equal(true)
```

</details>

#### keeps malformed @layer (no brace) text as-is

- keeps malformed @layer (no brace) text as-is
- Verify: keeps malformed @layer (no brace) text as-is
   - Expected: br_flatten_layer_blocks("@layer base") contains `@layer base`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-BROWSER_ENGINE
step("keeps malformed @layer (no brace) text as-is")
step("Verify: keeps malformed @layer (no brace) text as-is")
expect(br_flatten_layer_blocks("@layer base").contains("@layer base")).to_equal(true)
```

</details>

#### flattens a &-nested rule into parent-combined selector

- flattens a &-nested rule into parent-combined selector
- Verify: flattens a &-nested rule into parent-combined selector
   - Expected: flat contains `a:hover`
   - Expected: flat contains `color: blue`
   - Expected: flat contains `color: red`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-BROWSER_ENGINE
step("flattens a &-nested rule into parent-combined selector")
step("Verify: flattens a &-nested rule into parent-combined selector")
val flat = br_flatten_simple_nested_rules("a { color: red; &:hover { color: blue } }")
expect(flat.contains("a:hover")).to_equal(true)
expect(flat.contains("color: blue")).to_equal(true)
expect(flat.contains("color: red")).to_equal(true)
```

</details>

#### leaves rules without & untouched

- leaves rules without & untouched
- Verify: leaves rules without & untouched
   - Expected: br_flatten_simple_nested_rules(css) equals `css`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-BROWSER_ENGINE
step("leaves rules without & untouched")
step("Verify: leaves rules without & untouched")
val css = "a { color: red }"
expect(br_flatten_simple_nested_rules(css)).to_equal(css)
```

</details>

#### combines nested selectors only when & is present and not at-rule

- combines nested selectors only when & is present and not at-rule
- Verify: combines nested selectors only when & is present and not at-rule
   - Expected: br_combine_nested_selector("a", "&:hover") equals `a:hover`
   - Expected: br_combine_nested_selector("a", "@media x") equals ``
   - Expected: br_combine_nested_selector("a", "b") equals ``
   - Expected: br_combine_nested_selector("a", "  ") equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-BROWSER_ENGINE
step("combines nested selectors only when & is present and not at-rule")
step("Verify: combines nested selectors only when & is present and not at-rule")
expect(br_combine_nested_selector("a", "&:hover")).to_equal("a:hover")
expect(br_combine_nested_selector("a", "@media x")).to_equal("")
expect(br_combine_nested_selector("a", "b")).to_equal("")
expect(br_combine_nested_selector("a", "  ")).to_equal("")
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 22 |
| Active scenarios | 22 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-BROWSER_ENGINE`
- `REQ-BROWSER-ENGINE-BROWSER-RENDERER-UTILS-COVERAGE-CLOSURE-SPEC-SPL-001`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `36d07da6d1852716112ace684ebea40c3f8b3cb4d95df8d66459288f18d45f1b`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `36d07da6d1852716112ace684ebea40c3f8b3cb4d95df8d66459288f18d45f1b`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `36d07da6d1852716112ace684ebea40c3f8b3cb4d95df8d66459288f18d45f1b`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **86/100**; effective score: **86/100**; blockers: **0**.

SSpec documentization score: 86/100
source: test/01_unit/browser_engine/browser_renderer_utils_coverage_closure_spec.spl
mirror: doc/06_spec/01_unit/browser_engine/browser_renderer_utils_coverage_closure_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/browser_engine/browser_renderer_utils_coverage_closure_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/browser_engine/browser_renderer_utils_coverage_closure_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/browser_engine/browser_renderer_utils_coverage_closure_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 24 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/browser_engine/browser_renderer_utils_coverage_closure_spec.spl:57:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'finds a char at/after start and returns the sentinel when absent' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/browser_engine/browser_renderer_utils_coverage_closure_spec.spl:66:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'finds a substring and returns the sentinel when absent' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/browser_engine/browser_renderer_utils_coverage_closure_spec.spl:75:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'matches nested parens and braces, sentinel when unbalanced' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
