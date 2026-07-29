# CSS selector and color production subset

> Keeps the WPT-derived compatibility corpus and adds exact semantic/layout,

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 60 | 60 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# CSS selector and color production subset

Keeps the WPT-derived compatibility corpus and adds exact semantic/layout,

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/03_system/feature/web_platform/css/selector_color_subset_spec.spl` |
| Updated | 2026-07-29 |
| Generator | `simple spipe-docgen` (Simple) |

Keeps the WPT-derived compatibility corpus and adds exact semantic/layout,
canonical Draw IR, and pixel evidence for functional selector specificity,
ordinary pseudo chains, `:where()` zero specificity, and recursion bounds.

## Scenarios

### WPT-derived CSS selector and color subset

### CSS selector basics

<details>
<summary>Advanced: covers type selector matching</summary>

#### covers type selector matching

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_renders_color("div { width: 12px; height: 8px; background-color: #2563eb; }", "<div></div>", 0xFF2563EBu32)).to_equal(true)
```

</details>


</details>

<details>
<summary>Advanced: covers universal selector matching</summary>

#### covers universal selector matching

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_renders_color("* { width: 12px; height: 8px; background-color: #0f766e; }", "<div></div>", 0xFF0F766Eu32)).to_equal(true)
```

</details>


</details>

<details>
<summary>Advanced: covers class selector matching</summary>

#### covers class selector matching

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_renders_color(".card { width: 12px; height: 8px; background-color: #16a34a; }", "<div class='card'></div>", 0xFF16A34Au32)).to_equal(true)
```

</details>


</details>

<details>
<summary>Advanced: covers id selector matching</summary>

#### covers id selector matching

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_renders_color("#hero { width: 12px; height: 8px; background-color: #dc2626; }", "<div id='hero'></div>", 0xFFDC2626u32)).to_equal(true)
```

</details>


</details>

<details>
<summary>Advanced: covers selector-list matching</summary>

#### covers selector-list matching

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_renders_color("section, .card { width: 12px; height: 8px; background-color: #0891b2; }", "<div class='card'></div>", 0xFF0891B2u32)).to_equal(true)
```

</details>


</details>

<details>
<summary>Advanced: covers tag class compound selector matching</summary>

#### covers tag class compound selector matching

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_renders_color("div.card { width: 12px; height: 8px; background-color: #7c3aed; }", "<div class='card'></div>", 0xFF7C3AEDu32)).to_equal(true)
```

</details>


</details>

<details>
<summary>Advanced: covers multi class selector matching</summary>

#### covers multi class selector matching

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_renders_color(".card.primary { width: 12px; height: 8px; background-color: #0f766e; }", "<div class='primary card'></div>", 0xFF0F766Eu32)).to_equal(true)
```

</details>


</details>

<details>
<summary>Advanced: covers tag id compound selector matching</summary>

#### covers tag id compound selector matching

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_renders_color("div#hero { width: 12px; height: 8px; background-color: #be123c; }", "<div id='hero'></div>", 0xFFBE123Cu32)).to_equal(true)
```

</details>


</details>

<details>
<summary>Advanced: covers later class rule ordering</summary>

#### covers later class rule ordering

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_renders_color(".card { width: 12px; height: 8px; background-color: #2563eb; } .card { background-color: #9333ea; }", "<div class='card'></div>", 0xFF9333EAu32)).to_equal(true)
```

</details>


</details>

<details>
<summary>Advanced: covers class selector token boundaries</summary>

#### covers class selector token boundaries

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_renders_color(".card-title { width: 12px; height: 8px; background-color: #2563eb; } .card { width: 12px; height: 8px; background-color: #ea580c; }", "<div class='card'></div>", 0xFFEA580Cu32)).to_equal(true)
```

</details>


</details>

<details>
<summary>Advanced: covers :is selector-list matching</summary>

#### covers :is selector-list matching

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_renders_color(":is(section, .card) { width: 12px; height: 8px; background-color: #2563eb; }", "<div class='card'></div>", 0xFF2563EBu32)).to_equal(true)
```

</details>


</details>

<details>
<summary>Advanced: covers :where selector-list matching</summary>

#### covers :where selector-list matching

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_renders_color(":where(section, .card) { width: 12px; height: 8px; background-color: #16a34a; }", "<div class='card'></div>", 0xFF16A34Au32)).to_equal(true)
```

</details>


</details>

<details>
<summary>Advanced: covers partial :not selector-list exclusion</summary>

#### covers partial :not selector-list exclusion

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_renders_color("div:not(.disabled, #archived) { width: 12px; height: 8px; background-color: #0891b2; }", "<div class='card'></div>", 0xFF0891B2u32)).to_equal(true)
```

</details>


</details>

<details>
<summary>Advanced: covers partial :has descendant matching</summary>

#### covers partial :has descendant matching

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_renders_color("div:has(.badge) { width: 12px; height: 8px; background-color: #7c3aed; }", "<div><span class='badge'></span></div>", 0xFF7C3AEDu32)).to_equal(true)
```

</details>


</details>

<details>
<summary>Advanced: covers partial :has direct child matching</summary>

#### covers partial :has direct child matching

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_renders_color("div:has(> .badge) { width: 12px; height: 8px; background-color: #0e7490; }", "<div><span class='badge'></span></div>", 0xFF0E7490u32)).to_equal(true)
expect(_renders_color("div:has(> .badge) { width: 12px; height: 8px; background-color: #0e7490; }", "<div><section><span class='badge'></span></section></div>", 0xFF0E7490u32)).to_equal(false)
```

</details>


</details>

<details>
<summary>Advanced: covers descendant combinator matching</summary>

#### covers descendant combinator matching

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_renders_color(".scope .target { width: 12px; height: 8px; background-color: #2563eb; }", "<section class='scope'><div class='target'></div></section>", 0xFF2563EBu32)).to_equal(true)
```

</details>


</details>

<details>
<summary>Advanced: covers descendant combinator sibling rejection</summary>

#### covers descendant combinator sibling rejection

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_renders_color(".scope .target { width: 12px; height: 8px; background-color: #ea580c; }", "<section class='scope'></section><div class='target'></div>", 0xFFEA580Cu32)).to_equal(false)
```

</details>


</details>

<details>
<summary>Advanced: covers direct child combinator matching</summary>

#### covers direct child combinator matching

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_renders_color("body > .target { width: 12px; height: 8px; background-color: #16a34a; }", "<div class='target'></div>", 0xFF16A34Au32)).to_equal(true)
```

</details>


</details>

<details>
<summary>Advanced: covers ancestor child combinator matching</summary>

#### covers ancestor child combinator matching

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_renders_color(".scope > .target { width: 12px; height: 8px; background-color: #0891b2; }", "<section class='scope'><div class='target'></div></section>", 0xFF0891B2u32)).to_equal(true)
```

</details>


</details>

<details>
<summary>Advanced: covers ancestor child combinator nested descendant rejection</summary>

#### covers ancestor child combinator nested descendant rejection

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_renders_color(".scope > .target { width: 12px; height: 8px; background-color: #be123c; }", "<section class='scope'><article><div class='target'></div></article></section>", 0xFFBE123Cu32)).to_equal(false)
```

</details>


</details>

<details>
<summary>Advanced: covers direct child combinator nested descendant rejection</summary>

#### covers direct child combinator nested descendant rejection

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_renders_color("body > .target { width: 12px; height: 8px; background-color: #dc2626; }", "<section><div class='target'></div></section>", 0xFFDC2626u32)).to_equal(false)
```

</details>


</details>

<details>
<summary>Advanced: covers adjacent sibling combinator matching</summary>

#### covers adjacent sibling combinator matching

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_renders_color(".source + .target { width: 12px; height: 8px; background-color: #7c3aed; }", "<div class='source'></div><div class='target'></div>", 0xFF7C3AEDu32)).to_equal(true)
```

</details>


</details>

<details>
<summary>Advanced: covers adjacent sibling combinator non-adjacent rejection</summary>

#### covers adjacent sibling combinator non-adjacent rejection

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_renders_color(".source + .target { width: 12px; height: 8px; background-color: #be123c; }", "<div class='source'></div><section></section><div class='target'></div>", 0xFFBE123Cu32)).to_equal(false)
```

</details>


</details>

<details>
<summary>Advanced: covers general sibling combinator matching</summary>

#### covers general sibling combinator matching

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_renders_color(".source ~ .target { width: 12px; height: 8px; background-color: #0d9488; }", "<div class='source'></div><section></section><div class='target'></div>", 0xFF0D9488u32)).to_equal(true)
```

</details>


</details>

<details>
<summary>Advanced: covers general sibling combinator preceding-source rejection</summary>

#### covers general sibling combinator preceding-source rejection

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_renders_color(".source ~ .target { width: 12px; height: 8px; background-color: #e11d48; }", "<div class='target'></div><div class='source'></div>", 0xFFE11D48u32)).to_equal(false)
```

</details>


</details>

<details>
<summary>Advanced: covers partial :empty selector matching</summary>

#### covers partial :empty selector matching

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_renders_color("div:empty { width: 12px; height: 8px; background-color: #0f766e; }", "<div></div>", 0xFF0F766Eu32)).to_equal(true)
```

</details>


</details>

<details>
<summary>Advanced: covers partial :first-child selector matching</summary>

#### covers partial :first-child selector matching

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_renders_color(".target:first-child { width: 12px; height: 8px; background-color: #1d4ed8; }", "<div class='target'></div><div></div>", 0xFF1D4ED8u32)).to_equal(true)
```

</details>


</details>

<details>
<summary>Advanced: covers partial :last-child selector matching</summary>

#### covers partial :last-child selector matching

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_renders_color(".target:last-child { width: 12px; height: 8px; background-color: #be123c; }", "<div></div><div class='target'></div>", 0xFFBE123Cu32)).to_equal(true)
```

</details>


</details>

<details>
<summary>Advanced: covers partial :only-child selector matching</summary>

#### covers partial :only-child selector matching

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_renders_color(".target:only-child { width: 12px; height: 8px; background-color: #9333ea; }", "<div class='target'></div>", 0xFF9333EAu32)).to_equal(true)
```

</details>


</details>

<details>
<summary>Advanced: covers partial :nth-child odd and even matching</summary>

#### covers partial :nth-child odd and even matching

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_renders_color("div:nth-child(even) { width: 12px; height: 8px; background-color: #0e7490; }", "<div></div><div></div>", 0xFF0E7490u32)).to_equal(true)
expect(_renders_color(".target:nth-child(odd) { width: 12px; height: 8px; background-color: #0e7490; }", "<div></div><div class='target'></div>", 0xFF0E7490u32)).to_equal(false)
```

</details>


</details>

<details>
<summary>Advanced: covers partial :nth-child an plus b matching</summary>

#### covers partial :nth-child an plus b matching

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val positive_formula = "2n" + r"+1"
val positive_rule = ".target:nth-child(" + positive_formula + ") { width: 12px; height: 8px; background-color: #7c2d12; }"
expect(_renders_color(positive_rule, "<div></div><div></div><div class='target'></div>", 0xFF7C2D12u32)).to_equal(true)
expect(_renders_color(positive_rule, "<div></div><div class='target'></div><div></div>", 0xFF7C2D12u32)).to_equal(false)
```

</details>


</details>

<details>
<summary>Advanced: covers simple rules nested inside CSS layer blocks</summary>

#### covers simple rules nested inside CSS layer blocks

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_renders_color("@layer components { .card { width: 12px; height: 8px; background-color: #0f766e; } }", "<div class='card'></div>", 0xFF0F766Eu32)).to_equal(true)
```

</details>


</details>

<details>
<summary>Advanced: covers simple parent selector CSS nesting</summary>

#### covers simple parent selector CSS nesting

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_renders_color(".card { &.primary { width: 12px; height: 8px; background-color: #7e22ce; } }", "<div class='card primary'></div>", 0xFF7E22CEu32)).to_equal(true)
```

</details>


</details>

<details>
<summary>Advanced: covers attribute presence selector matching</summary>

#### covers attribute presence selector matching

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_renders_color("[data-card] { width: 12px; height: 8px; background-color: #0e7490; }", "<div data-card='true'></div>", 0xFF0E7490u32)).to_equal(true)
```

</details>


</details>

<details>
<summary>Advanced: covers exact attribute value selector matching</summary>

#### covers exact attribute value selector matching

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_renders_color("div[data-state='active'] { width: 12px; height: 8px; background-color: #4d7c0f; }", "<div data-state='active'></div>", 0xFF4D7C0Fu32)).to_equal(true)
```

</details>


</details>

<details>
<summary>Advanced: covers exact quoted attribute value selectors containing spaces</summary>

#### covers exact quoted attribute value selectors containing spaces

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_renders_color("[data-label='primary action'] { width: 12px; height: 8px; background-color: #0f766e; }", "<div data-label='primary action'></div>", 0xFF0F766Eu32)).to_equal(true)
```

</details>


</details>

<details>
<summary>Advanced: covers attribute prefix selector matching</summary>

#### covers attribute prefix selector matching

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_renders_color("div[data-route^='/app'] { width: 12px; height: 8px; background-color: #0f5e9c; }", "<div data-route='/app/home'></div>", 0xFF0F5E9Cu32)).to_equal(true)
```

</details>


</details>

<details>
<summary>Advanced: covers attribute suffix selector matching</summary>

#### covers attribute suffix selector matching

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_renders_color("div[data-route$='/settings'] { width: 12px; height: 8px; background-color: #065f46; }", "<div data-route='/app/settings'></div>", 0xFF065F46u32)).to_equal(true)
expect(_renders_color("div[data-route$='/settings'] { width: 12px; height: 8px; background-color: #065f46; }", "<div data-route='/app/settings/profile'></div>", 0xFF065F46u32)).to_equal(false)
```

</details>


</details>

<details>
<summary>Advanced: covers attribute substring selector matching</summary>

#### covers attribute substring selector matching

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_renders_color("[data-tags*='beta'] { width: 12px; height: 8px; background-color: #9d174d; }", "<div data-tags='alpha-beta-release'></div>", 0xFF9D174Du32)).to_equal(true)
```

</details>


</details>

<details>
<summary>Advanced: covers attribute whitespace token selector matching</summary>

#### covers attribute whitespace token selector matching

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_renders_color("[data-flags~='selected'] { width: 12px; height: 8px; background-color: #7c2d12; }", "<div data-flags='primary selected visible'></div>", 0xFF7C2D12u32)).to_equal(true)
```

</details>


</details>

<details>
<summary>Advanced: covers attribute dash match selector matching</summary>

#### covers attribute dash match selector matching

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_renders_color("div[lang|='en'] { width: 12px; height: 8px; background-color: #155e75; }", "<div lang='en-US'></div>", 0xFF155E75u32)).to_equal(true)
```

</details>


</details>

<details>
<summary>Advanced: covers case insensitive attribute selector matching</summary>

#### covers case insensitive attribute selector matching

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_renders_color("div[data-mode='dialog' i] { width: 12px; height: 8px; background-color: #4338ca; }", "<div data-mode='Dialog'></div>", 0xFF4338CAu32)).to_equal(true)
```

</details>


</details>

<details>
<summary>Advanced: covers explicit case sensitive attribute selector matching</summary>

#### covers explicit case sensitive attribute selector matching

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_renders_color("div[data-mode='Dialog' s] { width: 12px; height: 8px; background-color: #1d4ed8; }", "<div data-mode='Dialog'></div>", 0xFF1D4ED8u32)).to_equal(true)
```

</details>


</details>

#### should score every functional and ordinary pseudo in a chain

- " is-target:is
   - Artifact capture: after_step
- " not-target:not
   - Artifact capture: after_step
- " has-target:has
   - Artifact capture: after_step
- " where-target:where
   - Artifact capture: after_step
- fail
   - Artifact capture: after_step
- node index >= inspected hit index styles len
   - Artifact capture: after_step
- node index >= inspected hit index boxes by len
   - Artifact capture: after_step
- fail
   - Artifact capture: after_step
- Choose winners with complete chained pseudo specificity
   - Artifact capture: after_step
   - Evidence: artifact verified by 1 expected check
   - Expected: inspected.hit_index.boxes.by[where_node] equals `24`
- Lower selector winners through canonical Draw IR
   - Artifact capture: after_step
- fail
   - Artifact capture: after_step
- fail
   - Artifact capture: after_step
- Read exact selector pixels through both renderers
   - Artifact capture: after_step
- raster shutdown
   - Artifact capture: after_step
   - Evidence: artifact verified by 3 expected checks
   - Expected: rendered.skipped_command_count equals `0`
   - Expected: rendered.pixels.len() equals `32 * 48`
   - Expected: compatibility_pixels equals `engine_pixels`


<details>
<summary>Executable SSpec</summary>

Runnable source: 128 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val html = (
    "<style>html,body{margin:0;background:#fff}" +
    "div{width:12px;height:8px}" +
    ".is-target:is(.chosen,#never):first-child{background:#dc2626}" +
    "#is-target{background:#2563eb}" +
    ".not-target:not(.disabled):nth-child(2){background:#16a34a}" +
    ".not-target{background:#ea580c}" +
    ".has-target:has(#has-child):nth-child(3){background:#9333ea}" +
    "#has-target{background:#0e7490}" +
    ".where-target:where(#where-target):nth-child(4){" +
    "background:#dc2626}" +
    "#where-target{background:#0e7490}</style>" +
    "<div id='is-target' class='is-target chosen'></div>" +
    "<div id='not-target' class='not-target'></div>" +
    "<div id='has-target' class='has-target'>" +
    "<span id='has-child'></span></div>" +
    "<div id='where-target' class='where-target'></div>"
)
val inspected = simple_web_layout_render_html_draw_ir_result(
    html, 32, 48
)
val is_node = _selector_node_index(
    inspected.hit_index.nodes, "is-target"
)
val not_node = _selector_node_index(
    inspected.hit_index.nodes, "not-target"
)
val has_node = _selector_node_index(
    inspected.hit_index.nodes, "has-target"
)
val where_node = _selector_node_index(
    inspected.hit_index.nodes, "where-target"
)
if (
    is_node < 0 or not_node < 0 or has_node < 0 or where_node < 0
):
    fail("missing required semantic node")
for node_index in [is_node, not_node, has_node, where_node]:
    if (
        node_index >= inspected.hit_index.styles.len() or
        node_index >= inspected.hit_index.boxes.by.len()
    ):
        fail("semantic node outside style/layout arrays")

step("Choose winners with complete chained pseudo specificity")
expect(inspected.hit_index.styles[is_node].bg).to_equal(
    0xFFDC2626u32
)
expect(inspected.hit_index.styles[not_node].bg).to_equal(
    0xFF16A34Au32
)
expect(inspected.hit_index.styles[has_node].bg).to_equal(
    0xFF9333EAu32
)
expect(inspected.hit_index.styles[where_node].bg).to_equal(
    0xFF0E7490u32
)
expect(inspected.hit_index.boxes.by[where_node]).to_equal(24)

step("Lower selector winners through canonical Draw IR")
val composition = inspected.composition
if composition.batches.len() == 0:
    fail("missing Draw IR batch")
val commands = composition.batches[0].commands
val is_index = _selector_command_index(commands, "is-target")
val not_index = _selector_command_index(commands, "not-target")
val has_index = _selector_command_index(commands, "has-target")
val where_index = _selector_command_index(commands, "where-target")
if (
    is_index < 0 or not_index < 0 or has_index < 0 or
    where_index < 0
):
    fail("missing required Draw IR command")
val is_target = commands[is_index]
val not_target = commands[not_index]
val has_target = commands[has_index]
val where_target = commands[where_index]
expect([
    is_target.x, is_target.y, is_target.width, is_target.height
]).to_equal([0, 0, 12, 8])
expect([
    not_target.x, not_target.y, not_target.width, not_target.height
]).to_equal([0, 8, 12, 8])
expect([
    has_target.x, has_target.y, has_target.width, has_target.height
]).to_equal([0, 16, 12, 8])
expect([
    where_target.x, where_target.y,
    where_target.width, where_target.height
]).to_equal([0, 24, 12, 8])
expect(_selector_style(
    is_target, "background-color"
)).to_equal("4292617766")
expect(_selector_style(
    not_target, "background-color"
)).to_equal("4279673674")
expect(_selector_style(
    has_target, "background-color"
)).to_equal("4287837162")
expect(_selector_style(
    where_target, "background-color"
)).to_equal("4279137424")

step("Read exact selector pixels through both renderers")
val raster = Engine2dCompositorBackend.create_named(
    32, 48, "software"
)
val rendered = raster.render_draw_ir_composition(composition, [])
raster.shutdown()
expect(rendered.skipped_command_count).to_equal(0)
expect(rendered.pixels.len()).to_equal(32 * 48)
val engine_pixels = rendered.pixels
val compatibility_pixels = BrowserRenderer.create(
    32, 48
).render_html_to_pixels(html).pixel_data
expect(_selector_pixel_at(
    engine_pixels, 32, 2, 2
)).to_equal(0xFFDC2626u32)
expect(_selector_pixel_at(
    engine_pixels, 32, 2, 10
)).to_equal(0xFF16A34Au32)
expect(_selector_pixel_at(
    engine_pixels, 32, 2, 18
)).to_equal(0xFF9333EAu32)
expect(_selector_pixel_at(
    engine_pixels, 32, 2, 26
)).to_equal(0xFF0E7490u32)
expect(compatibility_pixels).to_equal(engine_pixels)
```

</details>

#### should admit selector depth thirty-two and reject deeper chains

- fail
   - Artifact capture: after_step
- node index >= inspected hit index styles len
   - Artifact capture: after_step
- node index >= inspected hit index boxes by len
   - Artifact capture: after_step
- fail
   - Artifact capture: after_step
- Apply only selectors within functional and chain budgets
   - Artifact capture: after_step
   - Evidence: artifact verified by 1 expected check
   - Expected: inspected.hit_index.boxes.by[chain_node] equals `16`
- Preserve selector boundary decisions in canonical Draw IR
   - Artifact capture: after_step
- fail
   - Artifact capture: after_step
- fail
   - Artifact capture: after_step
- Read exact selector boundary pixels through both renderers
   - Artifact capture: after_step
- raster shutdown
   - Artifact capture: after_step
   - Evidence: artifact verified by 3 expected checks
   - Expected: rendered.skipped_command_count equals `0`
   - Expected: rendered.pixels.len() equals `32 * 32`
   - Expected: compatibility_pixels equals `engine_pixels`


<details>
<summary>Executable SSpec</summary>

Runnable source: 96 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val admitted = _nested_selector(32, "depth-limit")
val rejected = _nested_selector(33, "depth-over")
var ordinary_chain = ".chain"
var count = 0
while count < 33:
    ordinary_chain = ordinary_chain + ":last-child"
    count = count + 1
val html = (
    "<style>html,body{margin:0;background:#fff}" +
    "div{width:12px;height:8px}" +
    "#depth-limit,#depth-over{background:#ea580c}" +
    ".chain{background:#16a34a}" +
    admitted + "{background:#9333ea}" +
    rejected + "{background:#9333ea}" +
    ordinary_chain + "{background:#dc2626}</style>" +
    "<div id='depth-limit'></div><div id='depth-over'></div>" +
    "<div id='chain' class='chain'></div>"
)
val inspected = simple_web_layout_render_html_draw_ir_result(
    html, 32, 32
)
val limit_node = _selector_node_index(
    inspected.hit_index.nodes, "depth-limit"
)
val over_node = _selector_node_index(
    inspected.hit_index.nodes, "depth-over"
)
val chain_node = _selector_node_index(
    inspected.hit_index.nodes, "chain"
)
if limit_node < 0 or over_node < 0 or chain_node < 0:
    fail("missing required semantic node")
for node_index in [limit_node, over_node, chain_node]:
    if (
        node_index >= inspected.hit_index.styles.len() or
        node_index >= inspected.hit_index.boxes.by.len()
    ):
        fail("semantic node outside style/layout arrays")

step("Apply only selectors within functional and chain budgets")
expect(inspected.hit_index.styles[limit_node].bg).to_equal(
    0xFF9333EAu32
)
expect(inspected.hit_index.styles[over_node].bg).to_equal(
    0xFFEA580Cu32
)
expect(inspected.hit_index.styles[chain_node].bg).to_equal(
    0xFF16A34Au32
)
expect(inspected.hit_index.boxes.by[chain_node]).to_equal(16)

step("Preserve selector boundary decisions in canonical Draw IR")
val composition = inspected.composition
if composition.batches.len() == 0:
    fail("missing Draw IR batch")
val commands = composition.batches[0].commands
val limit_index = _selector_command_index(commands, "depth-limit")
val over_index = _selector_command_index(commands, "depth-over")
val chain_index = _selector_command_index(commands, "chain")
if limit_index < 0 or over_index < 0 or chain_index < 0:
    fail("missing required Draw IR command")
val limit = commands[limit_index]
val over = commands[over_index]
val chain = commands[chain_index]
expect(_selector_style(
    limit, "background-color"
)).to_equal("4287837162")
expect(_selector_style(
    over, "background-color"
)).to_equal("4293548044")
expect(_selector_style(
    chain, "background-color"
)).to_equal("4279673674")

step("Read exact selector boundary pixels through both renderers")
val raster = Engine2dCompositorBackend.create_named(
    32, 32, "software"
)
val rendered = raster.render_draw_ir_composition(composition, [])
raster.shutdown()
expect(rendered.skipped_command_count).to_equal(0)
expect(rendered.pixels.len()).to_equal(32 * 32)
val engine_pixels = rendered.pixels
val compatibility_pixels = BrowserRenderer.create(
    32, 32
).render_html_to_pixels(html).pixel_data
expect(_selector_pixel_at(
    engine_pixels, 32, 2, 2
)).to_equal(0xFF9333EAu32)
expect(_selector_pixel_at(
    engine_pixels, 32, 2, 10
)).to_equal(0xFFEA580Cu32)
expect(_selector_pixel_at(
    engine_pixels, 32, 2, 18
)).to_equal(0xFF16A34Au32)
expect(compatibility_pixels).to_equal(engine_pixels)
```

</details>

#### should admit sixteen selector options and reject seventeen

- " list16:is
   - Artifact capture: after_step
- " list17:is
   - Artifact capture: after_step
- "#has16:has
   - Artifact capture: after_step
- "#has17:has
   - Artifact capture: after_step
- fail
   - Artifact capture: after_step
- node index >= inspected hit index styles len
   - Artifact capture: after_step
- node index >= inspected hit index boxes by len
   - Artifact capture: after_step
- fail
   - Artifact capture: after_step
- Invalidate whole over-cap and malformed selectors
   - Artifact capture: after_step
- Preserve exact option-cap decisions in canonical Draw IR
   - Artifact capture: after_step
- fail
   - Artifact capture: after_step
- fail
   - Artifact capture: after_step
- Read exact cap pixels and prove residual red is absent
   - Artifact capture: after_step
- raster shutdown
   - Artifact capture: after_step
   - Evidence: artifact verified by 3 expected checks
   - Expected: rendered.skipped_command_count equals `0`
   - Expected: rendered.pixels.len() equals `32 * 72`
   - Expected: compatibility_pixels equals `engine_pixels`


<details>
<summary>Executable SSpec</summary>

Runnable source: 186 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val list16 = _selector_option_list(16)
val list17 = _selector_option_list(17)
val has16 = _selector_list_with_match(16, "#child16")
val has17 = _selector_list_with_match(17, "#child17")
val groups16 = _selector_list_with_match(16, "#group16")
val groups17 = _selector_list_with_match(17, "#group17")
val html = (
    "<style>html,body{margin:0;background:#fff}" +
    "div{width:12px;height:8px;background:#16a34a}" +
    ".list16:is(" + list16 + "){background:#dc2626}" +
    ".list17:is(" + list17 + "){background:#dc2626}" +
    "#has16:has(" + has16 + "){background:#dc2626}" +
    "#has17:has(" + has17 + "){background:#dc2626}" +
    groups16 + "{background:#dc2626}" +
    groups17 + "{background:#dc2626}" +
    ".prefix:hovered{background:#dc2626}" +
    ".malformed:is(.malformed{background:#dc2626}</style>" +
    "<div id='list16' class='list16 chosen'></div>" +
    "<div id='list17' class='list17 chosen'></div>" +
    "<div id='prefix' class='prefix'></div>" +
    "<div id='malformed' class='malformed'></div>" +
    "<div id='has16'><span id='child16'></span></div>" +
    "<div id='has17'><span id='child17'></span></div>" +
    "<div id='group16'></div><div id='group17'></div>"
)
val inspected = simple_web_layout_render_html_draw_ir_result(
    html, 32, 72
)
val list16_node = _selector_node_index(
    inspected.hit_index.nodes, "list16"
)
val list17_node = _selector_node_index(
    inspected.hit_index.nodes, "list17"
)
val prefix_node = _selector_node_index(
    inspected.hit_index.nodes, "prefix"
)
val malformed_node = _selector_node_index(
    inspected.hit_index.nodes, "malformed"
)
val has16_node = _selector_node_index(
    inspected.hit_index.nodes, "has16"
)
val has17_node = _selector_node_index(
    inspected.hit_index.nodes, "has17"
)
val group16_node = _selector_node_index(
    inspected.hit_index.nodes, "group16"
)
val group17_node = _selector_node_index(
    inspected.hit_index.nodes, "group17"
)
if (
    list16_node < 0 or list17_node < 0 or prefix_node < 0 or
    malformed_node < 0 or has16_node < 0 or has17_node < 0 or
    group16_node < 0 or group17_node < 0
):
    fail("missing required semantic node")
for node_index in [
    list16_node, list17_node, prefix_node, malformed_node,
    has16_node, has17_node, group16_node, group17_node
]:
    if (
        node_index >= inspected.hit_index.styles.len() or
        node_index >= inspected.hit_index.boxes.by.len()
    ):
        fail("semantic node outside style/layout arrays")

step("Invalidate whole over-cap and malformed selectors")
expect(inspected.hit_index.styles[list16_node].bg).to_equal(
    0xFFDC2626u32
)
expect(inspected.hit_index.styles[list17_node].bg).to_equal(
    0xFF16A34Au32
)
expect(inspected.hit_index.styles[prefix_node].bg).to_equal(
    0xFF16A34Au32
)
expect(inspected.hit_index.styles[malformed_node].bg).to_equal(
    0xFF16A34Au32
)
expect(inspected.hit_index.styles[has16_node].bg).to_equal(
    0xFFDC2626u32
)
expect(inspected.hit_index.styles[has17_node].bg).to_equal(
    0xFF16A34Au32
)
expect(inspected.hit_index.styles[group16_node].bg).to_equal(
    0xFFDC2626u32
)
expect(inspected.hit_index.styles[group17_node].bg).to_equal(
    0xFF16A34Au32
)

step("Preserve exact option-cap decisions in canonical Draw IR")
val composition = inspected.composition
if composition.batches.len() == 0:
    fail("missing Draw IR batch")
val commands = composition.batches[0].commands
val list16_index = _selector_command_index(commands, "list16")
val list17_index = _selector_command_index(commands, "list17")
val prefix_index = _selector_command_index(commands, "prefix")
val malformed_index = _selector_command_index(commands, "malformed")
val has16_index = _selector_command_index(commands, "has16")
val has17_index = _selector_command_index(commands, "has17")
val group16_index = _selector_command_index(commands, "group16")
val group17_index = _selector_command_index(commands, "group17")
if (
    list16_index < 0 or list17_index < 0 or prefix_index < 0 or
    malformed_index < 0 or has16_index < 0 or has17_index < 0 or
    group16_index < 0 or group17_index < 0
):
    fail("missing required Draw IR command")
val list16_command = commands[list16_index]
val list17_command = commands[list17_index]
val prefix = commands[prefix_index]
val malformed = commands[malformed_index]
val has16_command = commands[has16_index]
val has17_command = commands[has17_index]
val group16_command = commands[group16_index]
val group17_command = commands[group17_index]
expect(_selector_style(
    list16_command, "background-color"
)).to_equal("4292617766")
expect(_selector_style(
    list17_command, "background-color"
)).to_equal("4279673674")
expect(_selector_style(
    prefix, "background-color"
)).to_equal("4279673674")
expect(_selector_style(
    malformed, "background-color"
)).to_equal("4279673674")
expect(_selector_style(
    has16_command, "background-color"
)).to_equal("4292617766")
expect(_selector_style(
    has17_command, "background-color"
)).to_equal("4279673674")
expect(_selector_style(
    group16_command, "background-color"
)).to_equal("4292617766")
expect(_selector_style(
    group17_command, "background-color"
)).to_equal("4279673674")

step("Read exact cap pixels and prove residual red is absent")
val raster = Engine2dCompositorBackend.create_named(
    32, 72, "software"
)
val rendered = raster.render_draw_ir_composition(composition, [])
raster.shutdown()
expect(rendered.skipped_command_count).to_equal(0)
expect(rendered.pixels.len()).to_equal(32 * 72)
val engine_pixels = rendered.pixels
val compatibility_pixels = BrowserRenderer.create(
    32, 72
).render_html_to_pixels(html).pixel_data
expect(_selector_pixel_at(
    engine_pixels, 32, 2, 2
)).to_equal(0xFFDC2626u32)
expect(_selector_pixel_at(
    engine_pixels, 32, 2, 10
)).to_equal(0xFF16A34Au32)
expect(_selector_pixel_at(
    engine_pixels, 32, 2, 18
)).to_equal(0xFF16A34Au32)
expect(_selector_pixel_at(
    engine_pixels, 32, 2, 26
)).to_equal(0xFF16A34Au32)
expect(_selector_pixel_at(
    engine_pixels, 32, 2, 34
)).to_equal(0xFFDC2626u32)
expect(_selector_pixel_at(
    engine_pixels, 32, 2, 42
)).to_equal(0xFF16A34Au32)
expect(_selector_pixel_at(
    engine_pixels, 32, 2, 50
)).to_equal(0xFFDC2626u32)
expect(_selector_pixel_at(
    engine_pixels, 32, 2, 58
)).to_equal(0xFF16A34Au32)
expect(_count_color(
    engine_pixels, 0xFFDC2626u32
)).to_equal(12 * 8 * 3)
expect(compatibility_pixels).to_equal(engine_pixels)
```

</details>

### CSS color and background basics

#### covers six digit hex color

- Render a body with a six-digit hexadecimal background color
- Verify the exact rendered color
   - Expected: _body_renders_color("background-color:#2563eb", 0xFF2563EBu32) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Render a body with a six-digit hexadecimal background color")
step("Verify the exact rendered color")
expect(_body_renders_color("background-color:#2563eb", 0xFF2563EBu32)).to_equal(true)
```

</details>

<details>
<summary>Advanced: covers shorthand hex color</summary>

#### covers shorthand hex color

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_body_renders_color("background-color:#0f8", 0xFF00FF88u32)).to_equal(true)
```

</details>


</details>

<details>
<summary>Advanced: covers legacy rgb function color</summary>

#### covers legacy rgb function color

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_body_renders_color("background-color:rgb(5, 150, 105)", 0xFF059669u32)).to_equal(true)
```

</details>


</details>

<details>
<summary>Advanced: covers modern space separated rgb function color</summary>

#### covers modern space separated rgb function color

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_body_renders_color("background-color:rgb(5 150 105)", 0xFF059669u32)).to_equal(true)
```

</details>


</details>

<details>
<summary>Advanced: covers rgba compositing over white</summary>

#### covers rgba compositing over white

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_body_renders_color("background-color:rgba(0, 0, 0, 0.5)", 0xFF808080u32)).to_equal(true)
```

</details>


</details>

<details>
<summary>Advanced: covers hsl function color</summary>

#### covers hsl function color

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_body_renders_color("background-color:hsl(120, 100%, 25%)", 0xFF008000u32)).to_equal(true)
```

</details>


</details>

<details>
<summary>Advanced: covers named CSS color</summary>

#### covers named CSS color

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_body_renders_color("background-color:rebeccapurple", 0xFF663399u32)).to_equal(true)
```

</details>


</details>

<details>
<summary>Advanced: covers transparent compositing to white</summary>

#### covers transparent compositing to white

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_body_renders_color("background-color:transparent", 0xFFFFFFFFu32)).to_equal(true)
```

</details>


</details>

<details>
<summary>Advanced: covers function color background shorthand</summary>

#### covers function color background shorthand

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_body_renders_color("background:rgb(5, 150, 105) no-repeat", 0xFF059669u32)).to_equal(true)
```

</details>


</details>

<details>
<summary>Advanced: covers color-first background shorthand</summary>

#### covers color-first background shorthand

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_body_renders_color("background:rebeccapurple no-repeat", 0xFF663399u32)).to_equal(true)
```

</details>


</details>

<details>
<summary>Advanced: covers url background shorthand fallback color</summary>

#### covers url background shorthand fallback color

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_body_renders_color("background:url(hero.png) #0f8 no-repeat", 0xFF00FF88u32)).to_equal(true)
```

</details>


</details>

<details>
<summary>Advanced: covers CSS custom property fallback colors</summary>

#### covers CSS custom property fallback colors

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_renders_color(".card { width: 12px; height: 8px; background-color: var(--missing-panel, #2563eb); }", "<div class='card'></div>", 0xFF2563EBu32)).to_equal(true)
```

</details>


</details>

<details>
<summary>Advanced: covers CSS custom property fallback colors in background shorthand</summary>

#### covers CSS custom property fallback colors in background shorthand

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_renders_color(".card { width: 12px; height: 8px; background: var(--missing-panel, #0891b2) no-repeat; }", "<div class='card'></div>", 0xFF0891B2u32)).to_equal(true)
```

</details>


</details>

<details>
<summary>Advanced: covers later background-color overriding shorthand</summary>

#### covers later background-color overriding shorthand

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_body_renders_color("background:#0f8; background-color:rebeccapurple", 0xFF663399u32)).to_equal(true)
```

</details>


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
