# Selector Color Subset Specification

> <details>

<!-- sdn-diagram:id=selector_color_subset_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=selector_color_subset_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

selector_color_subset_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=selector_color_subset_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 57 | 57 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Selector Color Subset Specification

## Scenarios

### WPT-derived CSS selector and color subset

#### CSS selector basics

#### covers type selector matching

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_renders_color("div { width: 12px; height: 8px; background-color: #2563eb; }", "<div></div>", 0xFF2563EBu32)).to_equal(true)
```

</details>

#### covers universal selector matching

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_renders_color("* { width: 12px; height: 8px; background-color: #0f766e; }", "<div></div>", 0xFF0F766Eu32)).to_equal(true)
```

</details>

#### covers class selector matching

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_renders_color(".card { width: 12px; height: 8px; background-color: #16a34a; }", "<div class='card'></div>", 0xFF16A34Au32)).to_equal(true)
```

</details>

#### covers id selector matching

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_renders_color("#hero { width: 12px; height: 8px; background-color: #dc2626; }", "<div id='hero'></div>", 0xFFDC2626u32)).to_equal(true)
```

</details>

#### covers selector-list matching

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_renders_color("section, .card { width: 12px; height: 8px; background-color: #0891b2; }", "<div class='card'></div>", 0xFF0891B2u32)).to_equal(true)
```

</details>

#### covers tag class compound selector matching

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_renders_color("div.card { width: 12px; height: 8px; background-color: #7c3aed; }", "<div class='card'></div>", 0xFF7C3AEDu32)).to_equal(true)
```

</details>

#### covers multi class selector matching

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_renders_color(".card.primary { width: 12px; height: 8px; background-color: #0f766e; }", "<div class='primary card'></div>", 0xFF0F766Eu32)).to_equal(true)
```

</details>

#### covers tag id compound selector matching

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_renders_color("div#hero { width: 12px; height: 8px; background-color: #be123c; }", "<div id='hero'></div>", 0xFFBE123Cu32)).to_equal(true)
```

</details>

#### covers later class rule ordering

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_renders_color(".card { width: 12px; height: 8px; background-color: #2563eb; } .card { background-color: #9333ea; }", "<div class='card'></div>", 0xFF9333EAu32)).to_equal(true)
```

</details>

#### covers class selector token boundaries

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_renders_color(".card-title { width: 12px; height: 8px; background-color: #2563eb; } .card { width: 12px; height: 8px; background-color: #ea580c; }", "<div class='card'></div>", 0xFFEA580Cu32)).to_equal(true)
```

</details>

#### covers :is selector-list matching

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_renders_color(":is(section, .card) { width: 12px; height: 8px; background-color: #2563eb; }", "<div class='card'></div>", 0xFF2563EBu32)).to_equal(true)
```

</details>

#### covers :where selector-list matching

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_renders_color(":where(section, .card) { width: 12px; height: 8px; background-color: #16a34a; }", "<div class='card'></div>", 0xFF16A34Au32)).to_equal(true)
```

</details>

#### covers partial :not selector-list exclusion

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_renders_color("div:not(.disabled, #archived) { width: 12px; height: 8px; background-color: #0891b2; }", "<div class='card'></div>", 0xFF0891B2u32)).to_equal(true)
```

</details>

#### covers partial :has descendant matching

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_renders_color("div:has(.badge) { width: 12px; height: 8px; background-color: #7c3aed; }", "<div><span class='badge'></span></div>", 0xFF7C3AEDu32)).to_equal(true)
```

</details>

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

#### covers descendant combinator matching

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_renders_color(".scope .target { width: 12px; height: 8px; background-color: #2563eb; }", "<section class='scope'><div class='target'></div></section>", 0xFF2563EBu32)).to_equal(true)
```

</details>

#### covers descendant combinator sibling rejection

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_renders_color(".scope .target { width: 12px; height: 8px; background-color: #ea580c; }", "<section class='scope'></section><div class='target'></div>", 0xFFEA580Cu32)).to_equal(false)
```

</details>

#### covers direct child combinator matching

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_renders_color("body > .target { width: 12px; height: 8px; background-color: #16a34a; }", "<div class='target'></div>", 0xFF16A34Au32)).to_equal(true)
```

</details>

#### covers ancestor child combinator matching

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_renders_color(".scope > .target { width: 12px; height: 8px; background-color: #0891b2; }", "<section class='scope'><div class='target'></div></section>", 0xFF0891B2u32)).to_equal(true)
```

</details>

#### covers ancestor child combinator nested descendant rejection

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_renders_color(".scope > .target { width: 12px; height: 8px; background-color: #be123c; }", "<section class='scope'><article><div class='target'></div></article></section>", 0xFFBE123Cu32)).to_equal(false)
```

</details>

#### covers direct child combinator nested descendant rejection

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_renders_color("body > .target { width: 12px; height: 8px; background-color: #dc2626; }", "<section><div class='target'></div></section>", 0xFFDC2626u32)).to_equal(false)
```

</details>

#### covers adjacent sibling combinator matching

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_renders_color(".source + .target { width: 12px; height: 8px; background-color: #7c3aed; }", "<div class='source'></div><div class='target'></div>", 0xFF7C3AEDu32)).to_equal(true)
```

</details>

#### covers adjacent sibling combinator non-adjacent rejection

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_renders_color(".source + .target { width: 12px; height: 8px; background-color: #be123c; }", "<div class='source'></div><section></section><div class='target'></div>", 0xFFBE123Cu32)).to_equal(false)
```

</details>

#### covers general sibling combinator matching

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_renders_color(".source ~ .target { width: 12px; height: 8px; background-color: #0d9488; }", "<div class='source'></div><section></section><div class='target'></div>", 0xFF0D9488u32)).to_equal(true)
```

</details>

#### covers general sibling combinator preceding-source rejection

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_renders_color(".source ~ .target { width: 12px; height: 8px; background-color: #e11d48; }", "<div class='target'></div><div class='source'></div>", 0xFFE11D48u32)).to_equal(false)
```

</details>

#### covers partial :empty selector matching

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_renders_color("div:empty { width: 12px; height: 8px; background-color: #0f766e; }", "<div></div>", 0xFF0F766Eu32)).to_equal(true)
```

</details>

#### covers partial :first-child selector matching

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_renders_color(".target:first-child { width: 12px; height: 8px; background-color: #1d4ed8; }", "<div class='target'></div><div></div>", 0xFF1D4ED8u32)).to_equal(true)
```

</details>

#### covers partial :last-child selector matching

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_renders_color(".target:last-child { width: 12px; height: 8px; background-color: #be123c; }", "<div></div><div class='target'></div>", 0xFFBE123Cu32)).to_equal(true)
```

</details>

#### covers partial :only-child selector matching

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_renders_color(".target:only-child { width: 12px; height: 8px; background-color: #9333ea; }", "<div class='target'></div>", 0xFF9333EAu32)).to_equal(true)
```

</details>

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

#### covers simple rules nested inside CSS layer blocks

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_renders_color("@layer components { .card { width: 12px; height: 8px; background-color: #0f766e; } }", "<div class='card'></div>", 0xFF0F766Eu32)).to_equal(true)
```

</details>

#### covers simple parent selector CSS nesting

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_renders_color(".card { &.primary { width: 12px; height: 8px; background-color: #7e22ce; } }", "<div class='card primary'></div>", 0xFF7E22CEu32)).to_equal(true)
```

</details>

#### covers attribute presence selector matching

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_renders_color("[data-card] { width: 12px; height: 8px; background-color: #0e7490; }", "<div data-card='true'></div>", 0xFF0E7490u32)).to_equal(true)
```

</details>

#### covers exact attribute value selector matching

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_renders_color("div[data-state='active'] { width: 12px; height: 8px; background-color: #4d7c0f; }", "<div data-state='active'></div>", 0xFF4D7C0Fu32)).to_equal(true)
```

</details>

#### covers exact quoted attribute value selectors containing spaces

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_renders_color("[data-label='primary action'] { width: 12px; height: 8px; background-color: #0f766e; }", "<div data-label='primary action'></div>", 0xFF0F766Eu32)).to_equal(true)
```

</details>

#### covers attribute prefix selector matching

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_renders_color("div[data-route^='/app'] { width: 12px; height: 8px; background-color: #0f5e9c; }", "<div data-route='/app/home'></div>", 0xFF0F5E9Cu32)).to_equal(true)
```

</details>

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

#### covers attribute substring selector matching

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_renders_color("[data-tags*='beta'] { width: 12px; height: 8px; background-color: #9d174d; }", "<div data-tags='alpha-beta-release'></div>", 0xFF9D174Du32)).to_equal(true)
```

</details>

#### covers attribute whitespace token selector matching

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_renders_color("[data-flags~='selected'] { width: 12px; height: 8px; background-color: #7c2d12; }", "<div data-flags='primary selected visible'></div>", 0xFF7C2D12u32)).to_equal(true)
```

</details>

#### covers attribute dash match selector matching

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_renders_color("div[lang|='en'] { width: 12px; height: 8px; background-color: #155e75; }", "<div lang='en-US'></div>", 0xFF155E75u32)).to_equal(true)
```

</details>

#### covers case insensitive attribute selector matching

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_renders_color("div[data-mode='dialog' i] { width: 12px; height: 8px; background-color: #4338ca; }", "<div data-mode='Dialog'></div>", 0xFF4338CAu32)).to_equal(true)
```

</details>

#### covers explicit case sensitive attribute selector matching

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_renders_color("div[data-mode='Dialog' s] { width: 12px; height: 8px; background-color: #1d4ed8; }", "<div data-mode='Dialog'></div>", 0xFF1D4ED8u32)).to_equal(true)
```

</details>

#### CSS color and background basics

#### covers six digit hex color

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_body_renders_color("background-color:#2563eb", 0xFF2563EBu32)).to_equal(true)
```

</details>

#### covers shorthand hex color

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_body_renders_color("background-color:#0f8", 0xFF00FF88u32)).to_equal(true)
```

</details>

#### covers legacy rgb function color

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_body_renders_color("background-color:rgb(5, 150, 105)", 0xFF059669u32)).to_equal(true)
```

</details>

#### covers modern space separated rgb function color

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_body_renders_color("background-color:rgb(5 150 105)", 0xFF059669u32)).to_equal(true)
```

</details>

#### covers rgba compositing over white

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_body_renders_color("background-color:rgba(0, 0, 0, 0.5)", 0xFF808080u32)).to_equal(true)
```

</details>

#### covers hsl function color

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_body_renders_color("background-color:hsl(120, 100%, 25%)", 0xFF008000u32)).to_equal(true)
```

</details>

#### covers named CSS color

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_body_renders_color("background-color:rebeccapurple", 0xFF663399u32)).to_equal(true)
```

</details>

#### covers transparent compositing to white

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_body_renders_color("background-color:transparent", 0xFFFFFFFFu32)).to_equal(true)
```

</details>

#### covers function color background shorthand

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_body_renders_color("background:rgb(5, 150, 105) no-repeat", 0xFF059669u32)).to_equal(true)
```

</details>

#### covers color-first background shorthand

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_body_renders_color("background:rebeccapurple no-repeat", 0xFF663399u32)).to_equal(true)
```

</details>

#### covers url background shorthand fallback color

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_body_renders_color("background:url(hero.png) #0f8 no-repeat", 0xFF00FF88u32)).to_equal(true)
```

</details>

#### covers CSS custom property fallback colors

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_renders_color(".card { width: 12px; height: 8px; background-color: var(--missing-panel, #2563eb); }", "<div class='card'></div>", 0xFF2563EBu32)).to_equal(true)
```

</details>

#### covers CSS custom property fallback colors in background shorthand

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_renders_color(".card { width: 12px; height: 8px; background: var(--missing-panel, #0891b2) no-repeat; }", "<div class='card'></div>", 0xFF0891B2u32)).to_equal(true)
```

</details>

#### covers later background-color overriding shorthand

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_body_renders_color("background:#0f8; background-color:rebeccapurple", 0xFF663399u32)).to_equal(true)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/03_system/feature/web_platform/css/selector_color_subset_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- WPT-derived CSS selector and color subset

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 57 |
| Active scenarios | 57 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
