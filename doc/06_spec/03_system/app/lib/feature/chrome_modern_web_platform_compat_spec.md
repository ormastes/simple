# Chrome Modern Web Platform Compat Specification

> Tests covering Chrome modern web platform compatibility plan.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 44 | 44 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Chrome Modern Web Platform Compat Specification

## Scenarios

### Chrome modern web platform compatibility plan

#### REQ-001 compatibility matrix

<details>
<summary>Advanced: should require HTML CSS DOM rendering and JavaScript matrix coverage</summary>

#### should require HTML CSS DOM rendering and JavaScript matrix coverage

</details>

#### should require explicit compatibility statuses

- should require explicit compatibility statuses


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should require explicit compatibility statuses")
val plan = _read(PLAN_PATH)
expect(plan).to_contain("`supported`, `partial`, `missing`, or `not-applicable`")
```

</details>

#### should gate migration on first WPT and Test262 subset selection

- should gate migration on first WPT and Test262 subset selection


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should gate migration on first WPT and Test262 subset selection")
val plan = _read(PLAN_PATH)
expect(plan).to_contain("identify the first WPT/Test262 subset to migrate")
```

</details>

#### REQ-002 WPT subset migration

#### should define a repeatable WPT subset import surface

- should define a repeatable WPT subset import surface


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should define a repeatable WPT subset import surface")
val plan = _read(PLAN_PATH)
expect(plan).to_contain("tools/wpt_to_spipe/")
expect(plan).to_contain("test/feature/web_platform/")
```

</details>

#### should provide the first executable WPT selector color subset

- should provide the first executable WPT selector color subset


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should provide the first executable WPT selector color subset")
val subset_plan = _read(WPT_SUBSET_PLAN_PATH)
val subset_spec = _read(WPT_SELECTOR_COLOR_SPEC_PATH)
expect(subset_plan).to_contain("selector_color_subset_spec.spl")
expect(subset_plan).to_contain("At least 25 selected WPT-shaped cases")
expect(subset_spec).to_contain("WPT-derived CSS selector and color subset")
expect(subset_spec).to_contain("covers partial :has descendant matching")
```

</details>

#### should cover selector color parser and rendering basics

- should cover selector color parser and rendering basics


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should cover selector color parser and rendering basics")
val plan = _read(PLAN_PATH)
expect(plan).to_contain("CSS selectors")
expect(plan).to_contain("CSS colors")
expect(plan).to_contain("HTML parser basics")
expect(plan).to_contain("Rendering basics")
```

</details>

#### should cover CSS custom property fallback colors in the WPT selector subset

- should cover CSS custom property fallback colors in the WPT selector subset


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should cover CSS custom property fallback colors in the WPT selector subset")
val spec = _read(WPT_SELECTOR_COLOR_SPEC_PATH)
expect(spec).to_contain("covers CSS custom property fallback colors")
expect(spec).to_contain("covers CSS custom property fallback colors in background shorthand")
```

</details>

#### should require at least twenty five WPT derived cases

- should require at least twenty five WPT derived cases


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should require at least twenty five WPT derived cases")
val plan = _read(PLAN_PATH)
expect(plan).to_contain("At least 25 selected WPT-derived cases")
```

</details>

#### REQ-003 Test262 subset migration

#### should define a repeatable Test262 subset import surface

- should define a repeatable Test262 subset import surface


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should define a repeatable Test262 subset import surface")
val plan = _read(PLAN_PATH)
expect(plan).to_contain("tools/test262_to_spipe/")
expect(plan).to_contain("test/js/test262_subset/")
```

</details>

#### should classify JavaScript conformance outcomes

- should classify JavaScript conformance outcomes


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should classify JavaScript conformance outcomes")
val plan = _read(PLAN_PATH)
expect(plan).to_contain("expected-pass, expected-fail, and unsupported-host")
```

</details>

#### should require at least fifty stable Test262 derived cases

- should require at least fifty stable Test262 derived cases


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should require at least fifty stable Test262 derived cases")
val plan = _read(PLAN_PATH)
expect(plan).to_contain("At least 50 selected Test262-derived cases")
```

</details>

#### REQ-004 supported feature evidence

#### should require SPipe or external suite mapping for supported features

- should require SPipe or external suite mapping for supported features


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val plan = _read(PLAN_PATH)
expect(plan).to_contain("Every supported feature has SPipe coverage or an explicit external-suite mapping")
```

</details>

#### should cover universal selectors in the WPT selector subset

- should cover universal selectors in the WPT selector subset


- Verify: should cover modern not selector behavior in renderer SPipe


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_read(WPT_SELECTOR_COLOR_SPEC_PATH)).to_contain("covers universal selector matching")
```

</details>

#### should cover modern is selector behavior in renderer SPipe

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_read(RENDERER_SPEC_PATH)).to_contain("applies :is selector lists in fallback pixels")
```

</details>

#### should cover modern where selector behavior in renderer SPipe

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_read(RENDERER_SPEC_PATH)).to_contain("applies :where selector lists in fallback pixels")
```

</details>

#### should cover modern not selector behavior in renderer SPipe

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should cover modern is selector behavior in renderer SPipe")
expect(_read(RENDERER_SPEC_PATH)).to_contain("applies :is selector lists in fallback pixels")
```

</details>

#### should cover modern where selector behavior in renderer SPipe

- should cover modern where selector behavior in renderer SPipe


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should cover modern where selector behavior in renderer SPipe")
expect(_read(RENDERER_SPEC_PATH)).to_contain("applies :where selector lists in fallback pixels")
```

</details>

#### should cover modern not selector behavior in renderer SPipe

- should cover modern not selector behavior in renderer SPipe


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should cover modern not selector behavior in renderer SPipe")
val spec = _read(RENDERER_SPEC_PATH)
expect(spec).to_contain("applies :not selector lists in fallback pixels")
expect(spec).to_contain("rejects :not selectors when an option matches")
```

</details>

#### should cover partial has selector behavior in renderer SPipe

- should cover partial has selector behavior in renderer SPipe


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should cover partial has selector behavior in renderer SPipe")
val spec = _read(RENDERER_SPEC_PATH)
expect(spec).to_contain("applies :has descendant selectors in fallback pixels")
expect(spec).to_contain("applies :has direct child selectors in fallback pixels")
expect(spec).to_contain("rejects :has direct child selectors for nested descendants")
expect(spec).to_contain("rejects :has selectors when no descendant option matches")
```

</details>

#### should cover bounded descendant combinators in the WPT selector subset

- should cover bounded descendant combinators in the WPT selector subset


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should cover bounded descendant combinators in the WPT selector subset")
val spec = _read(WPT_SELECTOR_COLOR_SPEC_PATH)
expect(spec).to_contain("covers descendant combinator matching")
expect(spec).to_contain("covers descendant combinator sibling rejection")
```

</details>

#### should cover bounded direct child combinators in the WPT selector subset

- should cover bounded direct child combinators in the WPT selector subset


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should cover bounded direct child combinators in the WPT selector subset")
val spec = _read(WPT_SELECTOR_COLOR_SPEC_PATH)
expect(spec).to_contain("covers direct child combinator matching")
expect(spec).to_contain("covers ancestor child combinator matching")
expect(spec).to_contain("covers ancestor child combinator nested descendant rejection")
expect(spec).to_contain("covers direct child combinator nested descendant rejection")
```

</details>

#### should cover bounded adjacent sibling combinators in the WPT selector subset

- should cover bounded adjacent sibling combinators in the WPT selector subset


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should cover bounded adjacent sibling combinators in the WPT selector subset")
val spec = _read(WPT_SELECTOR_COLOR_SPEC_PATH)
expect(spec).to_contain("covers adjacent sibling combinator matching")
expect(spec).to_contain("covers adjacent sibling combinator non-adjacent rejection")
```

</details>

#### should cover bounded general sibling combinators in the WPT selector subset

- should cover bounded general sibling combinators in the WPT selector subset


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should cover bounded general sibling combinators in the WPT selector subset")
val spec = _read(WPT_SELECTOR_COLOR_SPEC_PATH)
expect(spec).to_contain("covers general sibling combinator matching")
expect(spec).to_contain("covers general sibling combinator preceding-source rejection")
```

</details>

#### should cover partial empty selector behavior in renderer SPipe

- should cover partial empty selector behavior in renderer SPipe


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should cover partial empty selector behavior in renderer SPipe")
val spec = _read(RENDERER_SPEC_PATH)
expect(spec).to_contain("applies :empty selectors in fallback pixels")
expect(spec).to_contain("rejects :empty selectors when the fallback div has content")
```

</details>

#### should cover partial first child selector behavior in renderer SPipe

- should cover partial first child selector behavior in renderer SPipe


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should cover partial first child selector behavior in renderer SPipe")
val spec = _read(RENDERER_SPEC_PATH)
expect(spec).to_contain("applies :first-child selectors in fallback pixels")
expect(spec).to_contain("rejects :first-child selectors for later fallback divs")
```

</details>

#### should cover partial last child selector behavior in renderer SPipe

- should cover partial last child selector behavior in renderer SPipe


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should cover partial last child selector behavior in renderer SPipe")
val spec = _read(RENDERER_SPEC_PATH)
expect(spec).to_contain("applies :last-child selectors in fallback pixels")
expect(spec).to_contain("rejects :last-child selectors for earlier fallback divs")
```

</details>

#### should cover partial only child selector behavior in renderer SPipe

- should cover partial only child selector behavior in renderer SPipe


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should cover partial only child selector behavior in renderer SPipe")
val spec = _read(RENDERER_SPEC_PATH)
expect(spec).to_contain("applies :only-child selectors in fallback pixels")
expect(spec).to_contain("rejects :only-child selectors when a sibling exists")
```

</details>

#### should cover partial nth child selector behavior in renderer SPipe

- should cover partial nth child selector behavior in renderer SPipe


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should cover partial nth child selector behavior in renderer SPipe")
val spec = _read(RENDERER_SPEC_PATH)
expect(spec).to_contain("applies :nth-child odd and even selectors in fallback pixels")
expect(spec).to_contain("rejects :nth-child odd selectors for even fallback nodes")
expect(spec).to_contain("applies :nth-child an plus b selectors in fallback pixels")
expect(spec).to_contain("rejects :nth-child an plus b selectors for non matching fallback nodes")
```

</details>

#### should cover simple CSS layer block behavior in renderer SPipe

- should cover simple CSS layer block behavior in renderer SPipe


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should cover simple CSS layer block behavior in renderer SPipe")
val spec = _read(RENDERER_SPEC_PATH)
expect(spec).to_contain("applies simple rules nested inside CSS layer blocks")
expect(spec).to_contain("applies functional selectors nested inside CSS layer blocks")
```

</details>

#### should cover simple CSS nesting behavior in renderer SPipe

- should cover simple CSS nesting behavior in renderer SPipe


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should cover simple CSS nesting behavior in renderer SPipe")
val spec = _read(RENDERER_SPEC_PATH)
expect(spec).to_contain("normalizes simple CSS nesting before fallback selector scans")
expect(spec).to_contain("applies simple CSS nesting with parent selector references")
expect(spec).to_contain("applies simple descendant rules from CSS nesting")
```

</details>

#### should cover basic attribute selector behavior in renderer SPipe

- should cover basic attribute selector behavior in renderer SPipe


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should cover basic attribute selector behavior in renderer SPipe")
val spec = _read(RENDERER_SPEC_PATH)
expect(spec).to_contain("applies attribute presence selectors in fallback pixels")
expect(spec).to_contain("applies exact attribute value selectors in fallback pixels")
expect(spec).to_contain("applies exact quoted attribute value selectors containing spaces")
expect(spec).to_contain("rejects exact attribute value selectors with different values")
```

</details>

#### should cover bounded attribute selector operator behavior in renderer SPipe

- should cover bounded attribute selector operator behavior in renderer SPipe


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should cover bounded attribute selector operator behavior in renderer SPipe")
val spec = _read(RENDERER_SPEC_PATH)
expect(spec).to_contain("applies attribute prefix selectors in fallback pixels")
expect(spec).to_contain("applies attribute suffix selectors in fallback pixels")
expect(spec).to_contain("rejects attribute suffix selectors without a matching suffix")
expect(spec).to_contain("applies attribute substring selectors in fallback pixels")
expect(spec).to_contain("applies attribute whitespace token selectors in fallback pixels")
expect(spec).to_contain("applies attribute dash match selectors in fallback pixels")
expect(spec).to_contain("rejects attribute dash match selectors without a boundary")
expect(spec).to_contain("applies case insensitive attribute selectors in fallback pixels")
expect(spec).to_contain("keeps attribute selectors case sensitive without the i flag")
expect(spec).to_contain("applies explicit case sensitive attribute selectors in fallback pixels")
expect(spec).to_contain("rejects explicit case sensitive attribute selectors with different case")
```

</details>

#### REQ-005 unsupported feature tracking

#### should explicitly reject full Chrome compatibility claims

- should explicitly reject full Chrome compatibility claims


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should explicitly reject full Chrome compatibility claims")
val audit = _read(AUDIT_PATH)
expect(audit).to_contain("Simple is not a full Chrome-compatible browser engine")
```

</details>

#### should require unsupported high value feature tracking

- should require unsupported high value feature tracking


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should require unsupported high value feature tracking")
val req = _read(FEATURE_REQ_PATH)
expect(req).to_contain("Every unsupported high-value feature shall be recorded")
```

</details>

#### should list broad WPT Test262 HTML and CSS gaps

- should list broad WPT Test262 HTML and CSS gaps


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should list broad WPT Test262 HTML and CSS gaps")
val audit = _read(AUDIT_PATH)
expect(audit).to_contain("No complete WPT migration yet")
expect(audit).to_contain("No complete Test262 migration yet")
expect(audit).to_contain("HTML modern element semantics")
expect(audit).to_contain("CSS modern layout systems")
```

</details>

#### REQ-006 verification gate

#### should define PASS WARN and FAIL states

- should define PASS WARN and FAIL states


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should define PASS WARN and FAIL states")
val plan = _read(PLAN_PATH)
expect(plan).to_contain("STATUS: PASS")
expect(plan).to_contain("STATUS: WARN")
expect(plan).to_contain("STATUS: FAIL")
```

</details>

#### should require the broad library check command

- should require the broad library check command


- Verify: should reject manual visual inspection as the only signal


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should require the broad library check command")
val plan = _read(PLAN_PATH)
expect(plan).to_contain("bin/simple check src/lib")
```

</details>

#### should reject manual visual inspection as the only signal

- should reject manual visual inspection as the only signal


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should reject manual visual inspection as the only signal")
val req = _read(FEATURE_REQ_PATH)
val nfr = _read(NFR_REQ_PATH)
expect(req).to_contain("without relying on manual visual inspection")
expect(nfr).to_contain("shall not depend on manual visual inspection")
```

</details>

#### REQ-007 initial modern CSS BDD slice

#### should implement is and where selector matching in style blocks

- should implement is and where selector matching in style blocks


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should implement is and where selector matching in style blocks")
val source = _read(STYLE_BLOCK_PATH)
expect(source).to_contain(":is() and :where()")
expect(source).to_contain("functional_selector_list_matches")
```

</details>

#### should avoid splitting fallback selector lists inside functional pseudos

- should avoid splitting fallback selector lists inside functional pseudos


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should avoid splitting fallback selector lists inside functional pseudos")
val source = _read(BROWSER_RENDERER_PATH)
expect(source).to_contain("paren_depth")
expect(source).to_contain("br_functional_selector_contains")
```

</details>

#### should implement partial not and has selector matching

- should implement partial not and has selector matching


<details>
<summary>Executable SSpec</summary>

Runnable source: 21 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should implement partial not and has selector matching")
val style_source = _read(STYLE_BLOCK_PATH)
val renderer_source = _read(BROWSER_RENDERER_PATH)
expect(style_source).to_contain("not_selector_list_matches")
expect(style_source).to_contain("has_descendant_selector_list_match")
expect(style_source).to_contain("node_has_direct_child_matching")
expect(renderer_source).to_contain("br_style_block_rule_for_has_descendant")
expect(renderer_source).to_contain("br_simple_direct_child_option_in_subtree")
expect(renderer_source).to_contain("br_selector_matches_not_self")
expect(style_source).to_contain("node_is_empty")
expect(renderer_source).to_contain("br_style_block_rule_for_empty_self")
expect(style_source).to_contain(":first-child")
expect(renderer_source).to_contain("br_style_block_rule_for_first_child_self")
expect(style_source).to_contain(":last-child")
expect(renderer_source).to_contain("br_style_block_rule_for_last_child_self")
expect(style_source).to_contain(":only-child")
expect(renderer_source).to_contain("br_style_block_rule_for_only_child_self")
expect(style_source).to_contain("nth_child_argument_matches")
expect(style_source).to_contain("nth_child_common_formula_matches")
expect(renderer_source).to_contain("br_style_block_rule_for_nth_child_self")
```

</details>

#### should flatten simple CSS layer blocks before existing rule scans

- should flatten simple CSS layer blocks before existing rule scans


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should flatten simple CSS layer blocks before existing rule scans")
val style_source = _read(STYLE_BLOCK_PATH)
val renderer_source = _read(BROWSER_RENDERER_PATH)
val subset_spec = _read(WPT_SELECTOR_COLOR_SPEC_PATH)
expect(style_source).to_contain("flatten_layer_blocks")
expect(renderer_source).to_contain("br_flatten_layer_blocks")
expect(subset_spec).to_contain("covers simple rules nested inside CSS layer blocks")
```

</details>

#### should flatten simple CSS nesting before existing rule scans

- should flatten simple CSS nesting before existing rule scans


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should flatten simple CSS nesting before existing rule scans")
val style_source = _read(STYLE_BLOCK_PATH)
val renderer_source = _read(BROWSER_RENDERER_PATH)
val subset_spec = _read(WPT_SELECTOR_COLOR_SPEC_PATH)
expect(style_source).to_contain("flatten_simple_nested_rules")
expect(renderer_source).to_contain("br_flatten_simple_nested_rules")
expect(subset_spec).to_contain("covers simple parent selector CSS nesting")
```

</details>

#### should implement basic attribute selector matching

- should implement basic attribute selector matching


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should implement basic attribute selector matching")
val style_source = _read(STYLE_BLOCK_PATH)
val renderer_source = _read(BROWSER_RENDERER_PATH)
val subset_spec = _read(WPT_SELECTOR_COLOR_SPEC_PATH)
expect(style_source).to_contain("attribute_selector_matches")
expect(style_source).to_contain("marker == \"$\"")
expect(renderer_source).to_contain("br_style_block_rule_for_attr_self")
expect(subset_spec).to_contain("covers attribute presence selector matching")
expect(subset_spec).to_contain("covers exact attribute value selector matching")
```

</details>

#### should implement bounded attribute selector operators

- should implement bounded attribute selector operators


<details>
<summary>Executable SSpec</summary>

Runnable source: 17 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should implement bounded attribute selector operators")
val style_source = _read(STYLE_BLOCK_PATH)
val renderer_source = _read(BROWSER_RENDERER_PATH)
val subset_spec = _read(WPT_SELECTOR_COLOR_SPEC_PATH)
expect(style_source).to_contain("sb_attr_value_matches")
expect(renderer_source).to_contain("br_attr_value_matches")
expect(subset_spec).to_contain("covers attribute prefix selector matching")
expect(subset_spec).to_contain("covers attribute substring selector matching")
expect(subset_spec).to_contain("covers attribute whitespace token selector matching")
expect(subset_spec).to_contain("covers attribute dash match selector matching")
expect(style_source).to_contain("sb_attr_has_i_flag")
expect(style_source).to_contain("sb_attr_has_s_flag")
expect(renderer_source).to_contain("br_attr_has_i_flag")
expect(renderer_source).to_contain("br_attr_has_s_flag")
expect(subset_spec).to_contain("covers case insensitive attribute selector matching")
expect(subset_spec).to_contain("covers explicit case sensitive attribute selector matching")
```

</details>

#### should trace the BDD slice through the system test plan

- should trace the BDD slice through the system test plan


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should trace the BDD slice through the system test plan")
val test_plan = _read(TEST_PLAN_PATH)
expect(test_plan).to_contain("REQ-007: Initial Modern CSS BDD Slice")
expect(test_plan).to_contain("attribute selector/operator, `:empty`, `:first-child`, `:last-child`, and `:only-child` examples should pass")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/03_system/app/lib/feature/chrome_modern_web_platform_compat_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering Chrome modern web platform compatibility plan.
- Chrome modern web platform compatibility plan

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 44 |
| Active scenarios | 44 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-SYSTEM`
- `REQ-001`
- `REQ-002`
- `REQ-003`
- `REQ-004`
- `REQ-005`
- `REQ-006`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `17205e404aa5256f27bcad6edb40609997f82920ff033b2a98a3ee0d6b706255`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `17205e404aa5256f27bcad6edb40609997f82920ff033b2a98a3ee0d6b706255`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `17205e404aa5256f27bcad6edb40609997f82920ff033b2a98a3ee0d6b706255`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **80/100**; effective score: **49/100**; blockers: **1**.

SSpec documentization score: 49/100
source: test/03_system/app/lib/feature/chrome_modern_web_platform_compat_spec.spl
mirror: doc/06_spec/03_system/app/lib/feature/chrome_modern_web_platform_compat_spec.md (current)
findings: 13 blockers: 1
  narrative=100 structure=60 oracle=100
  traceability=60 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
  raw=80; blocker cap makes effective=49
doc/06_spec/03_system/app/lib/feature/chrome_modern_web_platform_compat_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/app/lib/feature/chrome_modern_web_platform_compat_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/app/lib/feature/chrome_modern_web_platform_compat_spec.spl:1:1: blocker SSDOC-TRC-003 [traceability] (-40): 6 declared requirement(s) have no scenario binding
  why: A requirement list without scenario evidence is inventory, not traceability.
  improve: Bind the stable requirement ID inside its executable scenario or explicit blocked case.
test/03_system/app/lib/feature/chrome_modern_web_platform_compat_spec.spl:32:1: warning SSDOC-BEH-001 [structure] (-10): scenario 'should require HTML CSS DOM rendering and JavaScript matrix coverage' has no visible step flow
  why: Ordered visible actions make the manual operable.
  improve: Add ordered step("...") calls for meaningful actions.
test/03_system/app/lib/feature/chrome_modern_web_platform_compat_spec.spl:32:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should require HTML CSS DOM rendering and JavaScript matrix coverage' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/03_system/app/lib/feature/chrome_modern_web_platform_compat_spec.spl:46:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should require explicit compatibility statuses' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/03_system/app/lib/feature/chrome_modern_web_platform_compat_spec.spl:46:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should require explicit compatibility statuses' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/app/lib/feature/chrome_modern_web_platform_compat_spec.spl:52:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should gate migration on first WPT and Test262 subset selection' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/03_system/app/lib/feature/chrome_modern_web_platform_compat_spec.spl:52:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should gate migration on first WPT and Test262 subset selection' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/app/lib/feature/chrome_modern_web_platform_compat_spec.spl:60:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should define a repeatable WPT subset import surface' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/03_system/app/lib/feature/chrome_modern_web_platform_compat_spec.spl:60:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should define a repeatable WPT subset import surface' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/app/lib/feature/chrome_modern_web_platform_compat_spec.spl:67:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should provide the first executable WPT selector color subset' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/03_system/app/lib/feature/chrome_modern_web_platform_compat_spec.spl:77:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should cover selector color parser and rendering basics' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
<!-- sspec-maintain:scorecard:end -->
