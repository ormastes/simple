# HTML Layout Renderer Declarations — Coverage Closure (U4.3, part 5: _declarations.spl)

> Purpose: Prove that sticky_top_inset_value (U4.3 closure).

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 18 | 18 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# HTML Layout Renderer Declarations — Coverage Closure (U4.3, part 5: _declarations.spl)

Purpose: Prove that sticky_top_inset_value (U4.3 closure).

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/01_unit/browser_engine/simple_web_html_layout_renderer_declarations_coverage_closure_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Purpose and audience
Purpose: Prove that sticky_top_inset_value (U4.3 closure).
Audience: compiler and tooling engineers who maintain this spec.

## Scenarios

### sticky_top_inset_value (U4.3 closure)

#### returns the sentinel only when position is sticky and the token is auto

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- returns the sentinel only when position is sticky and the token is auto
- Verify: returns the sentinel only when position is sticky and the token is auto
   - Expected: sticky_top_inset_value("auto", 5, true) equals `SIMPLE_WEB_STICKY_TOP_AUTO`
   - Expected: sticky_top_inset_value("auto", 5, false) equals `5`
   - Expected: sticky_top_inset_value("10px", 10, true) equals `10`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-BROWSER_ENGINE
step("returns the sentinel only when position is sticky and the token is auto")
step("Verify: returns the sentinel only when position is sticky and the token is auto")
# @req: REQ-BROWSER-ENGINE-SIMPLE-WEB-HTML-LAYOUT-RENDERER-DECLARATIONS-COVERAGE-CLOSURE-SPEC-SPL-001
expect(sticky_top_inset_value("auto", 5, true)).to_equal(SIMPLE_WEB_STICKY_TOP_AUTO)
expect(sticky_top_inset_value("auto", 5, false)).to_equal(5)
expect(sticky_top_inset_value("10px", 10, true)).to_equal(10)
```

</details>

### border_spacing_px (U4.3 closure)

#### parses px values, accepts bare zero, rejects malformed tokens

- parses px values, accepts bare zero, rejects malformed tokens
- Verify: parses px values, accepts bare zero, rejects malformed tokens
   - Expected: border_spacing_px("0") equals `0`
   - Expected: border_spacing_px("12px") equals `12`
   - Expected: border_spacing_px("12") equals `-1`
   - Expected: border_spacing_px("px") equals `-1`
   - Expected: border_spacing_px("1x2px") equals `-1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-BROWSER_ENGINE
step("parses px values, accepts bare zero, rejects malformed tokens")
step("Verify: parses px values, accepts bare zero, rejects malformed tokens")
expect(border_spacing_px("0")).to_equal(0)
expect(border_spacing_px("12px")).to_equal(12)
expect(border_spacing_px("12")).to_equal(-1)
expect(border_spacing_px("px")).to_equal(-1)
expect(border_spacing_px("1x2px")).to_equal(-1)
```

</details>

### _background_has_image_syntax (U4.3 closure)

#### detects any recognized image-function syntax and rejects plain colors

- detects any recognized image-function syntax and rejects plain colors
- Verify: detects any recognized image-function syntax and rejects plain colors
   - Expected: _background_has_image_syntax("linear-gradient(red, blue)") is true
   - Expected: _background_has_image_syntax("url(a.png)") is true
   - Expected: _background_has_image_syntax("red") is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-BROWSER_ENGINE
step("detects any recognized image-function syntax and rejects plain colors")
step("Verify: detects any recognized image-function syntax and rejects plain colors")
expect(_background_has_image_syntax("linear-gradient(red, blue)")).to_equal(true)
expect(_background_has_image_syntax("url(a.png)")).to_equal(true)
expect(_background_has_image_syntax("red")).to_equal(false)
```

</details>

### _background_is_exact_typed_linear_layer (U4.3 closure)

#### accepts a single linear-gradient layer and an optional trailing base color

- accepts a single linear-gradient layer and an optional trailing base color
- Verify: accepts a single linear-gradient layer and an optional trailing base color
   - Expected: _background_is_exact_typed_linear_layer("linear-gradient(red, blue)", 1u32, 2u32, true) is true
   - Expected: _background_is_exact_typed_linear_layer("linear-gradient(red, blue), red", 1u32, 2u32, true) is true
   - Expected: _background_is_exact_typed_linear_layer("linear-gradient(red, blue)", 0u32, 2u32, true) is false
   - Expected: _background_is_exact_typed_linear_layer("red", 1u32, 2u32, true) is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-BROWSER_ENGINE
step("accepts a single linear-gradient layer and an optional trailing base color")
step("Verify: accepts a single linear-gradient layer and an optional trailing base color")
expect(_background_is_exact_typed_linear_layer("linear-gradient(red, blue)", 1u32, 2u32, true)).to_equal(true)
expect(_background_is_exact_typed_linear_layer("linear-gradient(red, blue), red", 1u32, 2u32, true)).to_equal(true)
expect(_background_is_exact_typed_linear_layer("linear-gradient(red, blue)", 0u32, 2u32, true)).to_equal(false)
expect(_background_is_exact_typed_linear_layer("red", 1u32, 2u32, true)).to_equal(false)
```

</details>

### _background_exact_single_url (U4.3 closure)

#### extracts a lone quoted or bare url() and rejects multi-layer/gradient values

- extracts a lone quoted or bare url() and rejects multi-layer/gradient values
- Verify: extracts a lone quoted or bare url() and rejects multi-layer/gradient values
   - Expected: _background_exact_single_url("url(a.png)") equals `a.png`
   - Expected: _background_exact_single_url("url('a.png')") equals `a.png`
   - Expected: _background_exact_single_url("url(a.png), url(b.png)") equals ``
   - Expected: _background_exact_single_url("linear-gradient(red, blue)") equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-BROWSER_ENGINE
step("extracts a lone quoted or bare url() and rejects multi-layer/gradient values")
step("Verify: extracts a lone quoted or bare url() and rejects multi-layer/gradient values")
expect(_background_exact_single_url("url(a.png)")).to_equal("a.png")
expect(_background_exact_single_url("url('a.png')")).to_equal("a.png")
expect(_background_exact_single_url("url(a.png), url(b.png)")).to_equal("")
expect(_background_exact_single_url("linear-gradient(red, blue)")).to_equal("")
```

</details>

### _padding_integer_px / _padding_integer_px_values (U4.3 closure)

#### parses a single px token and a whitespace-separated list, capped by maximum

- parses a single px token and a whitespace-separated list, capped by maximum
- Verify: parses a single px token and a whitespace-separated list, capped by maximum
   - Expected: _padding_integer_px("0") equals `0`
   - Expected: _padding_integer_px("4px") equals `4`
   - Expected: _padding_integer_px("4") equals `-1`
   - Expected: two.len() equals `2`
   - Expected: two[0] equals `1`
   - Expected: two[1] equals `2`
   - Expected: _padding_integer_px_values("1px 2px 3px 4px 5px", 4).len() equals `0`
   - Expected: _padding_integer_px_values("1px bogus", 4).len() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-BROWSER_ENGINE
step("parses a single px token and a whitespace-separated list, capped by maximum")
step("Verify: parses a single px token and a whitespace-separated list, capped by maximum")
expect(_padding_integer_px("0")).to_equal(0)
expect(_padding_integer_px("4px")).to_equal(4)
expect(_padding_integer_px("4")).to_equal(-1)
val two = _padding_integer_px_values("1px 2px", 4)
expect(two.len()).to_equal(2)  # oracle: 2 — named expected value from the requirement
expect(two[0]).to_equal(1)  # oracle: 1 — named expected value from the requirement
expect(two[1]).to_equal(2)  # oracle: 2 — named expected value from the requirement
expect(_padding_integer_px_values("1px 2px 3px 4px 5px", 4).len()).to_equal(0)
expect(_padding_integer_px_values("1px bogus", 4).len()).to_equal(0)
```

</details>

### _resolve_authored_padding (U4.3 closure)

#### expands the padding shorthand and per-side longhands over the initial box

- expands the padding shorthand and per-side longhands over the initial box
- Verify: expands the padding shorthand and per-side longhands over the initial box
   - Expected: shorthand equals `(1, 2, 3, 4)`
   - Expected: longhand equals `(9, 0, 0, 0)`
   - Expected: logical equals `(0, 6, 0, 5)`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-BROWSER_ENGINE
step("expands the padding shorthand and per-side longhands over the initial box")
step("Verify: expands the padding shorthand and per-side longhands over the initial box")
val shorthand = _resolve_authored_padding(["padding", "1px 2px 3px 4px"], 0, 0, 0, 0)
expect(shorthand).to_equal((1, 2, 3, 4))
val longhand = _resolve_authored_padding(["padding-top", "9px"], 0, 0, 0, 0)
expect(longhand).to_equal((9, 0, 0, 0))
val logical = _resolve_authored_padding(["padding-inline", "5px 6px"], 0, 0, 0, 0)
expect(logical).to_equal((0, 6, 0, 5))
```

</details>

### _background_exact_url_value / _background_two_url_plan (U4.3 closure)

#### validates a single-url() wrapper and builds a two-layer serialization plan

- validates a single-url() wrapper and builds a two-layer serialization plan
- Verify: validates a single-url() wrapper and builds a two-layer serialization plan
   - Expected: _background_exact_url_value("url(a.png)") equals `a.png`
   - Expected: _background_exact_url_value("red") equals ``
   - Expected: plan.starts_with("two-url-v1\na.png\nb.png") is true
   - Expected: rejected equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-BROWSER_ENGINE
step("validates a single-url() wrapper and builds a two-layer serialization plan")
step("Verify: validates a single-url() wrapper and builds a two-layer serialization plan")
expect(_background_exact_url_value("url(a.png)")).to_equal("a.png")
expect(_background_exact_url_value("red")).to_equal("")
val plan = _background_two_url_plan(
    "url(a.png), url(b.png)", "no-repeat", "10px", "0 0",
    10, 0, 0, 0, "border-box", "border-box", "scroll",
)
expect(plan.starts_with("two-url-v1\na.png\nb.png")).to_equal(true)
val rejected = _background_two_url_plan(
    "url(a.png)", "no-repeat", "10px", "0 0",
    10, 0, 0, 0, "border-box", "border-box", "scroll",
)
expect(rejected).to_equal("")
```

</details>

### _background_position_value / _background_position_pair (U4.3 closure)

#### maps position keywords/percentages to internal sentinels and resolves ordered pairs

- maps position keywords/percentages to internal sentinels and resolves ordered pairs
- Verify: maps position keywords/percentages to internal sentinels and resolves ordered pairs
   - Expected: _background_position_value("left", true) equals `-1000`
   - Expected: _background_position_value("center", true) equals `-1050`
   - Expected: _background_position_value("right", true) equals `-1100`
   - Expected: _background_position_value("25%", true) equals `-1025`
   - Expected: pair[0] equals `-1000`
   - Expected: pair[1] equals `_background_position_value("top", false)`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-BROWSER_ENGINE
step("maps position keywords/percentages to internal sentinels and resolves ordered pairs")
step("Verify: maps position keywords/percentages to internal sentinels and resolves ordered pairs")
expect(_background_position_value("left", true)).to_equal(-1000)
expect(_background_position_value("center", true)).to_equal(-1050)
expect(_background_position_value("right", true)).to_equal(-1100)
expect(_background_position_value("25%", true)).to_equal(-1025)
val pair = _background_position_pair("top", "left")
expect(pair[0]).to_equal(-1000)  # oracle: -1000 — named expected value from the requirement
expect(pair[1]).to_equal(_background_position_value("top", false))
```

</details>

### _background_shorthand_tokens / token classifiers (U4.3 closure)

#### tokenizes on whitespace and slash while respecting parens, and classifies each token kind

- tokenizes on whitespace and slash while respecting parens, and classifies each token kind
- Verify: tokenizes on whitespace and slash while respecting parens, and classifies each token kind
   - Expected: tokens.len() equals `4`
   - Expected: tokens[0] equals `url(a`
   - Expected: tokens[1] equals `b)`
   - Expected: tokens[2] equals `/`
   - Expected: tokens[3] equals `10px`
   - Expected: _background_box_token("border-box") is true
   - Expected: _background_box_token("bogus") is false
   - Expected: _background_position_token("left") is true
   - Expected: _background_position_token("10px") is true
   - Expected: _background_position_token("bogus") is false
   - Expected: _background_size_token("auto") is true
   - Expected: _background_size_token("10px") is true
   - Expected: _background_size_token("bogus") is false
   - Expected: _background_color_token("transparent") is true
   - Expected: _background_color_token("bogus") is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 19 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-BROWSER_ENGINE
step("tokenizes on whitespace and slash while respecting parens, and classifies each token kind")
step("Verify: tokenizes on whitespace and slash while respecting parens, and classifies each token kind")
val tokens = _background_shorthand_tokens("url(a b) / 10px 20px")
expect(tokens.len()).to_equal(4)  # oracle: 4 — named expected value from the requirement
expect(tokens[0]).to_equal("url(a")
expect(tokens[1]).to_equal("b)")
expect(tokens[2]).to_equal("/")
expect(tokens[3]).to_equal("10px")
expect(_background_box_token("border-box")).to_equal(true)
expect(_background_box_token("bogus")).to_equal(false)
expect(_background_position_token("left")).to_equal(true)
expect(_background_position_token("10px")).to_equal(true)
expect(_background_position_token("bogus")).to_equal(false)
expect(_background_size_token("auto")).to_equal(true)
expect(_background_size_token("10px")).to_equal(true)
expect(_background_size_token("bogus")).to_equal(false)
expect(_background_color_token("transparent")).to_equal(true)
expect(_background_color_token("bogus")).to_equal(false)
```

</details>

### _parse_background_shorthand (U4.3 closure)

#### parses a valid shorthand into a BackgroundShorthand and rejects multi-layer values

- parses a valid shorthand into a BackgroundShorthand and rejects multi-layer values
- Verify: parses a valid shorthand into a BackgroundShorthand and rejects multi-layer values
   - Expected: ok.valid is true
   - Expected: ok.image_uri equals `a.png`
   - Expected: ok.repeat equals `no-repeat`
   - Expected: bad.valid is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-BROWSER_ENGINE
step("parses a valid shorthand into a BackgroundShorthand and rejects multi-layer values")
step("Verify: parses a valid shorthand into a BackgroundShorthand and rejects multi-layer values")
val ok = _parse_background_shorthand("url(a.png) no-repeat center / 10px")
expect(ok.valid).to_equal(true)
expect(ok.image_uri).to_equal("a.png")
expect(ok.repeat).to_equal("no-repeat")
val bad = _parse_background_shorthand("linear-gradient(red, blue), url(a.png)")
expect(bad.valid).to_equal(false)
```

</details>

### _decl_tbl_all_dispatch_handled / _decl_tbl_resolve_writing_mode (U4.3 closure)

#### reports whether every decl in the table has a known property id, and resolves writing-mode

- reports whether every decl in the table has a known property id, and resolves writing-mode
- Verify: reports whether every decl in the table has a known property id, and resolves writing-mode
   - Expected: _decl_tbl_all_dispatch_handled(["color", "red"]) is true
   - Expected: _decl_tbl_all_dispatch_handled(["not-a-real-prop", "x"]) is false
   - Expected: _decl_tbl_resolve_writing_mode("horizontal-tb", ["writing-mode", "vertical-rl"]) equals `vertical-rl`
   - Expected: _decl_tbl_resolve_writing_mode("horizontal-tb", ["writing-mode", "bogus"]) equals `horizontal-tb`
   - Expected: _decl_tbl_resolve_writing_mode("horizontal-tb", []) equals `horizontal-tb`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-BROWSER_ENGINE
step("reports whether every decl in the table has a known property id, and resolves writing-mode")
step("Verify: reports whether every decl in the table has a known property id, and resolves writing-mode")
expect(_decl_tbl_all_dispatch_handled(["color", "red"])).to_equal(true)
expect(_decl_tbl_all_dispatch_handled(["not-a-real-prop", "x"])).to_equal(false)
expect(_decl_tbl_resolve_writing_mode("horizontal-tb", ["writing-mode", "vertical-rl"])).to_equal("vertical-rl")
expect(_decl_tbl_resolve_writing_mode("horizontal-tb", ["writing-mode", "bogus"])).to_equal("horizontal-tb")
expect(_decl_tbl_resolve_writing_mode("horizontal-tb", [])).to_equal("horizontal-tb")
```

</details>

### parse_supported_nonnegative_px / decl_tbl_get_last_valid_nonnegative_px (U4.3 closure)

#### parses nonnegative px lengths and finds the last valid entry for a property

- parses nonnegative px lengths and finds the last valid entry for a property
- Verify: parses nonnegative px lengths and finds the last valid entry for a property
   - Expected: parse_supported_nonnegative_px("10px") equals `10`
   - Expected: parse_supported_nonnegative_px("10") equals `10`
   - Expected: parse_supported_nonnegative_px("-5px") equals `-1`
   - Expected: parse_supported_nonnegative_px("") equals `-1`
   - Expected: value equals `10px`
   - Expected: true is false
   - Expected: missing equals `nil`


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-BROWSER_ENGINE
step("parses nonnegative px lengths and finds the last valid entry for a property")
step("Verify: parses nonnegative px lengths and finds the last valid entry for a property")
expect(parse_supported_nonnegative_px("10px")).to_equal(10)
expect(parse_supported_nonnegative_px("10")).to_equal(10)
expect(parse_supported_nonnegative_px("-5px")).to_equal(-1)
expect(parse_supported_nonnegative_px("")).to_equal(-1)
val found = decl_tbl_get_last_valid_nonnegative_px(["width", "5px", "width", "10px"], "width")
if val Some(value) = found:
    expect(value).to_equal("10px")
else:
    expect(true).to_equal(false)
val missing = decl_tbl_get_last_valid_nonnegative_px(["height", "5px"], "width")
expect(missing).to_equal(nil)
```

</details>

### parse_supported_outline_shorthand_width_px (U4.3 closure)

#### accepts zero and positive px widths, rejects non-positive/malformed values

- accepts zero and positive px widths, rejects non-positive/malformed values
- Verify: accepts zero and positive px widths, rejects non-positive/malformed values
   - Expected: parse_supported_outline_shorthand_width_px("0") equals `0`
   - Expected: parse_supported_outline_shorthand_width_px("0px") equals `0`
   - Expected: parse_supported_outline_shorthand_width_px("3px") equals `3`
   - Expected: parse_supported_outline_shorthand_width_px("-3px") equals `-1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-BROWSER_ENGINE
step("accepts zero and positive px widths, rejects non-positive/malformed values")
step("Verify: accepts zero and positive px widths, rejects non-positive/malformed values")
expect(parse_supported_outline_shorthand_width_px("0")).to_equal(0)
expect(parse_supported_outline_shorthand_width_px("0px")).to_equal(0)
expect(parse_supported_outline_shorthand_width_px("3px")).to_equal(3)
expect(parse_supported_outline_shorthand_width_px("-3px")).to_equal(-1)
```

</details>

### resolve_writing_mode_decls (U4.3 closure)

#### returns current when writing-mode is absent/over-quota, else the resolved value

- returns current when writing-mode is absent/over-quota, else the resolved value
- Verify: returns current when writing-mode is absent/over-quota, else the resolved value
   - Expected: resolve_writing_mode_decls("horizontal-tb", "") equals `horizontal-tb`
   - Expected: resolve_writing_mode_decls("horizontal-tb", "color:red") equals `horizontal-tb`
   - Expected: resolve_writing_mode_decls("horizontal-tb", "writing-mode:vertical-rl") equals `vertical-rl`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-BROWSER_ENGINE
step("returns current when writing-mode is absent/over-quota, else the resolved value")
step("Verify: returns current when writing-mode is absent/over-quota, else the resolved value")
expect(resolve_writing_mode_decls("horizontal-tb", "")).to_equal("horizontal-tb")
expect(resolve_writing_mode_decls("horizontal-tb", "color:red")).to_equal("horizontal-tb")
expect(resolve_writing_mode_decls("horizontal-tb", "writing-mode:vertical-rl")).to_equal("vertical-rl")
```

</details>

### normalized_grid_positive_int / normalized_grid_track_list (U4.3 closure)

#### parses digit-only integers and builds a validated px/fr track list

- parses digit-only integers and builds a validated px/fr track list
- Verify: parses digit-only integers and builds a validated px/fr track list
   - Expected: normalized_grid_positive_int("42") equals `42`
   - Expected: normalized_grid_positive_int("4x") equals `0`
   - Expected: normalized_grid_positive_int("") equals `0`
   - Expected: normalized_grid_track_list("10px 20px") equals `10px 20px`
   - Expected: normalized_grid_track_list("1fr 2fr") equals `1fr 2fr`
   - Expected: normalized_grid_track_list("10px bogus") equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-BROWSER_ENGINE
step("parses digit-only integers and builds a validated px/fr track list")
step("Verify: parses digit-only integers and builds a validated px/fr track list")
expect(normalized_grid_positive_int("42")).to_equal(42)
expect(normalized_grid_positive_int("4x")).to_equal(0)
expect(normalized_grid_positive_int("")).to_equal(0)
expect(normalized_grid_track_list("10px 20px")).to_equal("10px 20px")
expect(normalized_grid_track_list("1fr 2fr")).to_equal("1fr 2fr")
expect(normalized_grid_track_list("10px bogus")).to_equal("")
```

</details>

### normalized_grid_placement (U4.3 closure)

#### resolves start-only, start/end, and start/span placements

- resolves start-only, start/end, and start/span placements
- Verify: resolves start-only, start/end, and start/span placements
   - Expected: normalized_grid_placement("2") equals `2`
   - Expected: normalized_grid_placement("2 / 4") equals `2 / 4`
   - Expected: normalized_grid_placement("2 / span 3") equals `2 / span 3`
   - Expected: normalized_grid_placement("0") equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-BROWSER_ENGINE
step("resolves start-only, start/end, and start/span placements")
step("Verify: resolves start-only, start/end, and start/span placements")
expect(normalized_grid_placement("2")).to_equal("2")
expect(normalized_grid_placement("2 / 4")).to_equal("2 / 4")
expect(normalized_grid_placement("2 / span 3")).to_equal("2 / span 3")
expect(normalized_grid_placement("0")).to_equal("")
```

</details>

### normalized_grid_area / normalized_grid_auto_flow / normalized_grid_template_areas (U4.3 closure)

#### passes through named areas, detects column auto-flow, and normalizes quoted area templates

- passes through named areas, detects column auto-flow, and normalizes quoted area templates
- Verify: passes through named areas, detects column auto-flow, and normalizes quoted area templates
   - Expected: normalized_grid_area("header") equals `header`
   - Expected: normalized_grid_area("auto") equals ``
   - Expected: normalized_grid_area("1 / 2") equals ``
   - Expected: normalized_grid_auto_flow("column") is true
   - Expected: normalized_grid_auto_flow("row") is false
   - Expected: normalized_grid_template_areas("\"a a\" \"b c\"") equals `a a|b c`
   - Expected: normalized_grid_template_areas("\"a a\" \"b\"") equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-BROWSER_ENGINE
step("passes through named areas, detects column auto-flow, and normalizes quoted area templates")
step("Verify: passes through named areas, detects column auto-flow, and normalizes quoted area templates")
expect(normalized_grid_area("header")).to_equal("header")
expect(normalized_grid_area("auto")).to_equal("")
expect(normalized_grid_area("1 / 2")).to_equal("")
expect(normalized_grid_auto_flow("column")).to_equal(true)
expect(normalized_grid_auto_flow("row")).to_equal(false)
expect(normalized_grid_template_areas("\"a a\" \"b c\"")).to_equal("a a|b c")
expect(normalized_grid_template_areas("\"a a\" \"b\"")).to_equal("")
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 18 |
| Active scenarios | 18 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-BROWSER_ENGINE`
- `REQ-BROWSER-ENGINE-SIMPLE-WEB-HTML-LAYOUT-RENDERER-DECLARATIONS-COVERAGE-CLOSURE-SPEC-SPL-001`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `2fc761d3d4764165c77bd093028957f37f8575be8088f66f6172d69a06779585`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `2fc761d3d4764165c77bd093028957f37f8575be8088f66f6172d69a06779585`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `2fc761d3d4764165c77bd093028957f37f8575be8088f66f6172d69a06779585`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **86/100**; effective score: **86/100**; blockers: **0**.

SSpec documentization score: 86/100
source: test/01_unit/browser_engine/simple_web_html_layout_renderer_declarations_coverage_closure_spec.spl
mirror: doc/06_spec/01_unit/browser_engine/simple_web_html_layout_renderer_declarations_coverage_closure_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/browser_engine/simple_web_html_layout_renderer_declarations_coverage_closure_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/browser_engine/simple_web_html_layout_renderer_declarations_coverage_closure_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/browser_engine/simple_web_html_layout_renderer_declarations_coverage_closure_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 27 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/browser_engine/simple_web_html_layout_renderer_declarations_coverage_closure_spec.spl:87:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'returns the sentinel only when position is sticky and the token is auto' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/browser_engine/simple_web_html_layout_renderer_declarations_coverage_closure_spec.spl:97:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'parses px values, accepts bare zero, rejects malformed tokens' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/browser_engine/simple_web_html_layout_renderer_declarations_coverage_closure_spec.spl:108:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'detects any recognized image-function syntax and rejects plain colors' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
