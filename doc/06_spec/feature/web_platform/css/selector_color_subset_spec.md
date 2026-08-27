# Selector Color Subset Specification

> Tests covering WPT-derived CSS selector and color subset.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 57 | 57 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Selector Color Subset Specification

## Scenarios

### WPT-derived CSS selector and color subset

#### CSS selector basics

<details>
<summary>Advanced: covers type selector matching</summary>

#### covers type selector matching _(slow)_

- covers type selector matching
   - Expected: _renders_color("div { width: 12px; height: 8px; background-color: #2563eb; }", "<div></div>", 0xFF2563EBu32) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("covers type selector matching")
expect(_renders_color("div { width: 12px; height: 8px; background-color: #2563eb; }", "<div></div>", 0xFF2563EBu32)).to_equal(true)
```

</details>


</details>

<details>
<summary>Advanced: covers universal selector matching</summary>

#### covers universal selector matching _(slow)_

- covers universal selector matching
   - Expected: _renders_color("* { width: 12px; height: 8px; background-color: #0f766e; }", "<div></div>", 0xFF0F766Eu32) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("covers universal selector matching")
expect(_renders_color("* { width: 12px; height: 8px; background-color: #0f766e; }", "<div></div>", 0xFF0F766Eu32)).to_equal(true)
```

</details>


</details>

<details>
<summary>Advanced: covers class selector matching</summary>

#### covers class selector matching _(slow)_

- covers class selector matching
   - Expected: _renders_color(".card { width: 12px; height: 8px; background-color: #16a34a; }", "<div class='card'></div>", 0xFF16A34Au32) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("covers class selector matching")
expect(_renders_color(".card { width: 12px; height: 8px; background-color: #16a34a; }", "<div class='card'></div>", 0xFF16A34Au32)).to_equal(true)
```

</details>


</details>

<details>
<summary>Advanced: covers id selector matching</summary>

#### covers id selector matching _(slow)_

- covers id selector matching
   - Expected: _renders_color("#hero { width: 12px; height: 8px; background-color: #dc2626; }", "<div id='hero'></div>", 0xFFDC2626u32) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("covers id selector matching")
expect(_renders_color("#hero { width: 12px; height: 8px; background-color: #dc2626; }", "<div id='hero'></div>", 0xFFDC2626u32)).to_equal(true)
```

</details>


</details>

<details>
<summary>Advanced: covers selector-list matching</summary>

#### covers selector-list matching _(slow)_

- covers selector-list matching
   - Expected: _renders_color("section, .card { width: 12px; height: 8px; background-color: #0891b2; }", "<div class='card'></div>", 0xFF0891B2u32) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("covers selector-list matching")
expect(_renders_color("section, .card { width: 12px; height: 8px; background-color: #0891b2; }", "<div class='card'></div>", 0xFF0891B2u32)).to_equal(true)
```

</details>


</details>

<details>
<summary>Advanced: covers tag class compound selector matching</summary>

#### covers tag class compound selector matching _(slow)_

- covers tag class compound selector matching
   - Expected: _renders_color("div.card { width: 12px; height: 8px; background-color: #7c3aed; }", "<div class='card'></div>", 0xFF7C3AEDu32) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("covers tag class compound selector matching")
expect(_renders_color("div.card { width: 12px; height: 8px; background-color: #7c3aed; }", "<div class='card'></div>", 0xFF7C3AEDu32)).to_equal(true)
```

</details>


</details>

<details>
<summary>Advanced: covers multi class selector matching</summary>

#### covers multi class selector matching _(slow)_

- covers multi class selector matching
   - Expected: _renders_color(".card.primary { width: 12px; height: 8px; background-color: #0f766e; }", "<div class='primary card'></div>", 0xFF0F766Eu32) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("covers multi class selector matching")
expect(_renders_color(".card.primary { width: 12px; height: 8px; background-color: #0f766e; }", "<div class='primary card'></div>", 0xFF0F766Eu32)).to_equal(true)
```

</details>


</details>

<details>
<summary>Advanced: covers tag id compound selector matching</summary>

#### covers tag id compound selector matching _(slow)_

- covers tag id compound selector matching
   - Expected: _renders_color("div#hero { width: 12px; height: 8px; background-color: #be123c; }", "<div id='hero'></div>", 0xFFBE123Cu32) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("covers tag id compound selector matching")
expect(_renders_color("div#hero { width: 12px; height: 8px; background-color: #be123c; }", "<div id='hero'></div>", 0xFFBE123Cu32)).to_equal(true)
```

</details>


</details>

<details>
<summary>Advanced: covers later class rule ordering</summary>

#### covers later class rule ordering _(slow)_

- covers later class rule ordering
   - Expected: _renders_color(".card { width: 12px; height: 8px; background-color: #2563eb; } .card { background-color: #9333ea; }", "<div class='card'></div>", 0xFF9333EAu32) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("covers later class rule ordering")
expect(_renders_color(".card { width: 12px; height: 8px; background-color: #2563eb; } .card { background-color: #9333ea; }", "<div class='card'></div>", 0xFF9333EAu32)).to_equal(true)
```

</details>


</details>

<details>
<summary>Advanced: covers class selector token boundaries</summary>

#### covers class selector token boundaries _(slow)_

- covers class selector token boundaries
   - Expected: _renders_color(".card-title { width: 12px; height: 8px; background-color: #2563eb; } .card { width: 12px; height: 8px; background-color: #ea580c; }", "<div class='card'></div>", 0xFFEA580Cu32) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("covers class selector token boundaries")
expect(_renders_color(".card-title { width: 12px; height: 8px; background-color: #2563eb; } .card { width: 12px; height: 8px; background-color: #ea580c; }", "<div class='card'></div>", 0xFFEA580Cu32)).to_equal(true)
```

</details>


</details>

<details>
<summary>Advanced: covers :is selector-list matching</summary>

#### covers :is selector-list matching _(slow)_

- covers :is selector-list matching
   - Expected: _renders_color(":is(section, .card) { width: 12px; height: 8px; background-color: #2563eb; }", "<div class='card'></div>", 0xFF2563EBu32) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("covers :is selector-list matching")
expect(_renders_color(":is(section, .card) { width: 12px; height: 8px; background-color: #2563eb; }", "<div class='card'></div>", 0xFF2563EBu32)).to_equal(true)
```

</details>


</details>

<details>
<summary>Advanced: covers :where selector-list matching</summary>

#### covers :where selector-list matching _(slow)_

- covers :where selector-list matching
   - Expected: _renders_color(":where(section, .card) { width: 12px; height: 8px; background-color: #16a34a; }", "<div class='card'></div>", 0xFF16A34Au32) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("covers :where selector-list matching")
expect(_renders_color(":where(section, .card) { width: 12px; height: 8px; background-color: #16a34a; }", "<div class='card'></div>", 0xFF16A34Au32)).to_equal(true)
```

</details>


</details>

<details>
<summary>Advanced: covers partial :not selector-list exclusion</summary>

#### covers partial :not selector-list exclusion _(slow)_

- covers partial :not selector-list exclusion
   - Expected: _renders_color("div:not(.disabled, #archived) { width: 12px; height: 8px; background-color: #0891b2; }", "<div class='card'></div>", 0xFF0891B2u32) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("covers partial :not selector-list exclusion")
expect(_renders_color("div:not(.disabled, #archived) { width: 12px; height: 8px; background-color: #0891b2; }", "<div class='card'></div>", 0xFF0891B2u32)).to_equal(true)
```

</details>


</details>

<details>
<summary>Advanced: covers partial :has descendant matching</summary>

#### covers partial :has descendant matching _(slow)_

- covers partial :has descendant matching
   - Expected: _renders_color("div:has(.badge) { width: 12px; height: 8px; background-color: #7c3aed; }", "<div><span class='badge'></span></div>", 0xFF7C3AEDu32) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("covers partial :has descendant matching")
expect(_renders_color("div:has(.badge) { width: 12px; height: 8px; background-color: #7c3aed; }", "<div><span class='badge'></span></div>", 0xFF7C3AEDu32)).to_equal(true)
```

</details>


</details>

<details>
<summary>Advanced: covers partial :has direct child matching</summary>

#### covers partial :has direct child matching _(slow)_

- covers partial :has direct child matching
   - Expected: _renders_color("div:has(> .badge) { width: 12px; height: 8px; background-color: #0e7490; }", "<div><span class='badge'></span></div>", 0xFF0E7490u32) is true
   - Expected: _renders_color("div:has(> .badge) { width: 12px; height: 8px; background-color: #0e7490; }", "<div><section><span class='badge'></span></section></div>", 0xFF0E7490u32) is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("covers partial :has direct child matching")
expect(_renders_color("div:has(> .badge) { width: 12px; height: 8px; background-color: #0e7490; }", "<div><span class='badge'></span></div>", 0xFF0E7490u32)).to_equal(true)
expect(_renders_color("div:has(> .badge) { width: 12px; height: 8px; background-color: #0e7490; }", "<div><section><span class='badge'></span></section></div>", 0xFF0E7490u32)).to_equal(false)
```

</details>


</details>

<details>
<summary>Advanced: covers descendant combinator matching</summary>

#### covers descendant combinator matching _(slow)_

- covers descendant combinator matching
   - Expected: _renders_color(".scope .target { width: 12px; height: 8px; background-color: #2563eb; }", "<section class='scope'><div class='target'></div></section>", 0xFF2563EBu32) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("covers descendant combinator matching")
expect(_renders_color(".scope .target { width: 12px; height: 8px; background-color: #2563eb; }", "<section class='scope'><div class='target'></div></section>", 0xFF2563EBu32)).to_equal(true)
```

</details>


</details>

<details>
<summary>Advanced: covers descendant combinator sibling rejection</summary>

#### covers descendant combinator sibling rejection _(slow)_

- covers descendant combinator sibling rejection
   - Expected: _renders_color(".scope .target { width: 12px; height: 8px; background-color: #ea580c; }", "<section class='scope'></section><div class='target'></div>", 0xFFEA580Cu32) is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("covers descendant combinator sibling rejection")
expect(_renders_color(".scope .target { width: 12px; height: 8px; background-color: #ea580c; }", "<section class='scope'></section><div class='target'></div>", 0xFFEA580Cu32)).to_equal(false)
```

</details>


</details>

<details>
<summary>Advanced: covers direct child combinator matching</summary>

#### covers direct child combinator matching _(slow)_

- covers direct child combinator matching
   - Expected: _renders_color("body > .target { width: 12px; height: 8px; background-color: #16a34a; }", "<div class='target'></div>", 0xFF16A34Au32) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("covers direct child combinator matching")
expect(_renders_color("body > .target { width: 12px; height: 8px; background-color: #16a34a; }", "<div class='target'></div>", 0xFF16A34Au32)).to_equal(true)
```

</details>


</details>

<details>
<summary>Advanced: covers ancestor child combinator matching</summary>

#### covers ancestor child combinator matching _(slow)_

- covers ancestor child combinator matching
   - Expected: _renders_color(".scope > .target { width: 12px; height: 8px; background-color: #0891b2; }", "<section class='scope'><div class='target'></div></section>", 0xFF0891B2u32) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("covers ancestor child combinator matching")
expect(_renders_color(".scope > .target { width: 12px; height: 8px; background-color: #0891b2; }", "<section class='scope'><div class='target'></div></section>", 0xFF0891B2u32)).to_equal(true)
```

</details>


</details>

<details>
<summary>Advanced: covers ancestor child combinator nested descendant rejection</summary>

#### covers ancestor child combinator nested descendant rejection _(slow)_

- covers ancestor child combinator nested descendant rejection
   - Expected: _renders_color(".scope > .target { width: 12px; height: 8px; background-color: #be123c; }", "<section class='scope'><article><div class='target'></div></article></section>", 0xFFBE123Cu32) is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("covers ancestor child combinator nested descendant rejection")
expect(_renders_color(".scope > .target { width: 12px; height: 8px; background-color: #be123c; }", "<section class='scope'><article><div class='target'></div></article></section>", 0xFFBE123Cu32)).to_equal(false)
```

</details>


</details>

<details>
<summary>Advanced: covers direct child combinator nested descendant rejection</summary>

#### covers direct child combinator nested descendant rejection _(slow)_

- covers direct child combinator nested descendant rejection
   - Expected: _renders_color("body > .target { width: 12px; height: 8px; background-color: #dc2626; }", "<section><div class='target'></div></section>", 0xFFDC2626u32) is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("covers direct child combinator nested descendant rejection")
expect(_renders_color("body > .target { width: 12px; height: 8px; background-color: #dc2626; }", "<section><div class='target'></div></section>", 0xFFDC2626u32)).to_equal(false)
```

</details>


</details>

<details>
<summary>Advanced: covers adjacent sibling combinator matching</summary>

#### covers adjacent sibling combinator matching _(slow)_

- covers adjacent sibling combinator matching
   - Expected: _renders_color(".source + .target { width: 12px; height: 8px; background-color: #7c3aed; }", "<div class='source'></div><div class='target'></div>", 0xFF7C3AEDu32) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("covers adjacent sibling combinator matching")
expect(_renders_color(".source + .target { width: 12px; height: 8px; background-color: #7c3aed; }", "<div class='source'></div><div class='target'></div>", 0xFF7C3AEDu32)).to_equal(true)
```

</details>


</details>

<details>
<summary>Advanced: covers adjacent sibling combinator non-adjacent rejection</summary>

#### covers adjacent sibling combinator non-adjacent rejection _(slow)_

- covers adjacent sibling combinator non-adjacent rejection
   - Expected: _renders_color(".source + .target { width: 12px; height: 8px; background-color: #be123c; }", "<div class='source'></div><section></section><div class='target'></div>", 0xFFBE123Cu32) is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("covers adjacent sibling combinator non-adjacent rejection")
expect(_renders_color(".source + .target { width: 12px; height: 8px; background-color: #be123c; }", "<div class='source'></div><section></section><div class='target'></div>", 0xFFBE123Cu32)).to_equal(false)
```

</details>


</details>

<details>
<summary>Advanced: covers general sibling combinator matching</summary>

#### covers general sibling combinator matching _(slow)_

- covers general sibling combinator matching
   - Expected: _renders_color(".source ~ .target { width: 12px; height: 8px; background-color: #0d9488; }", "<div class='source'></div><section></section><div class='target'></div>", 0xFF0D9488u32) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("covers general sibling combinator matching")
expect(_renders_color(".source ~ .target { width: 12px; height: 8px; background-color: #0d9488; }", "<div class='source'></div><section></section><div class='target'></div>", 0xFF0D9488u32)).to_equal(true)
```

</details>


</details>

<details>
<summary>Advanced: covers general sibling combinator preceding-source rejection</summary>

#### covers general sibling combinator preceding-source rejection _(slow)_

- covers general sibling combinator preceding-source rejection
   - Expected: _renders_color(".source ~ .target { width: 12px; height: 8px; background-color: #e11d48; }", "<div class='target'></div><div class='source'></div>", 0xFFE11D48u32) is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("covers general sibling combinator preceding-source rejection")
expect(_renders_color(".source ~ .target { width: 12px; height: 8px; background-color: #e11d48; }", "<div class='target'></div><div class='source'></div>", 0xFFE11D48u32)).to_equal(false)
```

</details>


</details>

<details>
<summary>Advanced: covers partial :empty selector matching</summary>

#### covers partial :empty selector matching _(slow)_

- covers partial :empty selector matching
   - Expected: _renders_color("div:empty { width: 12px; height: 8px; background-color: #0f766e; }", "<div></div>", 0xFF0F766Eu32) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("covers partial :empty selector matching")
expect(_renders_color("div:empty { width: 12px; height: 8px; background-color: #0f766e; }", "<div></div>", 0xFF0F766Eu32)).to_equal(true)
```

</details>


</details>

<details>
<summary>Advanced: covers partial :first-child selector matching</summary>

#### covers partial :first-child selector matching _(slow)_

- covers partial :first-child selector matching
   - Expected: _renders_color(".target:first-child { width: 12px; height: 8px; background-color: #1d4ed8; }", "<div class='target'></div><div></div>", 0xFF1D4ED8u32) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("covers partial :first-child selector matching")
expect(_renders_color(".target:first-child { width: 12px; height: 8px; background-color: #1d4ed8; }", "<div class='target'></div><div></div>", 0xFF1D4ED8u32)).to_equal(true)
```

</details>


</details>

<details>
<summary>Advanced: covers partial :last-child selector matching</summary>

#### covers partial :last-child selector matching _(slow)_

- covers partial :last-child selector matching
   - Expected: _renders_color(".target:last-child { width: 12px; height: 8px; background-color: #be123c; }", "<div></div><div class='target'></div>", 0xFFBE123Cu32) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("covers partial :last-child selector matching")
expect(_renders_color(".target:last-child { width: 12px; height: 8px; background-color: #be123c; }", "<div></div><div class='target'></div>", 0xFFBE123Cu32)).to_equal(true)
```

</details>


</details>

<details>
<summary>Advanced: covers partial :only-child selector matching</summary>

#### covers partial :only-child selector matching _(slow)_

- covers partial :only-child selector matching
   - Expected: _renders_color(".target:only-child { width: 12px; height: 8px; background-color: #9333ea; }", "<div class='target'></div>", 0xFF9333EAu32) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("covers partial :only-child selector matching")
expect(_renders_color(".target:only-child { width: 12px; height: 8px; background-color: #9333ea; }", "<div class='target'></div>", 0xFF9333EAu32)).to_equal(true)
```

</details>


</details>

<details>
<summary>Advanced: covers partial :nth-child odd and even matching</summary>

#### covers partial :nth-child odd and even matching _(slow)_

- covers partial :nth-child odd and even matching
   - Expected: _renders_color("div:nth-child(even) { width: 12px; height: 8px; background-color: #0e7490; }", "<div></div><div></div>", 0xFF0E7490u32) is true
   - Expected: _renders_color(".target:nth-child(odd) { width: 12px; height: 8px; background-color: #0e7490; }", "<div></div><div class='target'></div>", 0xFF0E7490u32) is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("covers partial :nth-child odd and even matching")
expect(_renders_color("div:nth-child(even) { width: 12px; height: 8px; background-color: #0e7490; }", "<div></div><div></div>", 0xFF0E7490u32)).to_equal(true)
expect(_renders_color(".target:nth-child(odd) { width: 12px; height: 8px; background-color: #0e7490; }", "<div></div><div class='target'></div>", 0xFF0E7490u32)).to_equal(false)
```

</details>


</details>

<details>
<summary>Advanced: covers partial :nth-child an plus b matching</summary>

#### covers partial :nth-child an plus b matching _(slow)_

- covers partial :nth-child an plus b matching
   - Expected: _renders_color(positive_rule, "<div></div><div></div><div class='target'></div>", 0xFF7C2D12u32) is true
   - Expected: _renders_color(positive_rule, "<div></div><div class='target'></div><div></div>", 0xFF7C2D12u32) is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("covers partial :nth-child an plus b matching")
val positive_formula = "2n" + r"+1"
val positive_rule = ".target:nth-child(" + positive_formula + ") { width: 12px; height: 8px; background-color: #7c2d12; }"
expect(_renders_color(positive_rule, "<div></div><div></div><div class='target'></div>", 0xFF7C2D12u32)).to_equal(true)
expect(_renders_color(positive_rule, "<div></div><div class='target'></div><div></div>", 0xFF7C2D12u32)).to_equal(false)
```

</details>


</details>

<details>
<summary>Advanced: covers simple rules nested inside CSS layer blocks</summary>

#### covers simple rules nested inside CSS layer blocks _(slow)_

- covers simple rules nested inside CSS layer blocks
   - Expected: _renders_color("@layer components { .card { width: 12px; height: 8px; background-color: #0f766e; } }", "<div class='card'></div>", 0xFF0F766Eu32) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("covers simple rules nested inside CSS layer blocks")
expect(_renders_color("@layer components { .card { width: 12px; height: 8px; background-color: #0f766e; } }", "<div class='card'></div>", 0xFF0F766Eu32)).to_equal(true)
```

</details>


</details>

<details>
<summary>Advanced: covers simple parent selector CSS nesting</summary>

#### covers simple parent selector CSS nesting _(slow)_

- covers simple parent selector CSS nesting
   - Expected: _renders_color(".card { &.primary { width: 12px; height: 8px; background-color: #7e22ce; } }", "<div class='card primary'></div>", 0xFF7E22CEu32) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("covers simple parent selector CSS nesting")
expect(_renders_color(".card { &.primary { width: 12px; height: 8px; background-color: #7e22ce; } }", "<div class='card primary'></div>", 0xFF7E22CEu32)).to_equal(true)
```

</details>


</details>

<details>
<summary>Advanced: covers attribute presence selector matching</summary>

#### covers attribute presence selector matching _(slow)_

- covers attribute presence selector matching
   - Expected: _renders_color("[data-card] { width: 12px; height: 8px; background-color: #0e7490; }", "<div data-card='true'></div>", 0xFF0E7490u32) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("covers attribute presence selector matching")
expect(_renders_color("[data-card] { width: 12px; height: 8px; background-color: #0e7490; }", "<div data-card='true'></div>", 0xFF0E7490u32)).to_equal(true)
```

</details>


</details>

<details>
<summary>Advanced: covers exact attribute value selector matching</summary>

#### covers exact attribute value selector matching _(slow)_

- covers exact attribute value selector matching
   - Expected: _renders_color("div[data-state='active'] { width: 12px; height: 8px; background-color: #4d7c0f; }", "<div data-state='active'></div>", 0xFF4D7C0Fu32) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("covers exact attribute value selector matching")
expect(_renders_color("div[data-state='active'] { width: 12px; height: 8px; background-color: #4d7c0f; }", "<div data-state='active'></div>", 0xFF4D7C0Fu32)).to_equal(true)
```

</details>


</details>

<details>
<summary>Advanced: covers exact quoted attribute value selectors containing spaces</summary>

#### covers exact quoted attribute value selectors containing spaces _(slow)_

- covers exact quoted attribute value selectors containing spaces
   - Expected: _renders_color("[data-label='primary action'] { width: 12px; height: 8px; background-color: #0f766e; }", "<div data-label='primary action'></div>", 0xFF0F766Eu32) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("covers exact quoted attribute value selectors containing spaces")
expect(_renders_color("[data-label='primary action'] { width: 12px; height: 8px; background-color: #0f766e; }", "<div data-label='primary action'></div>", 0xFF0F766Eu32)).to_equal(true)
```

</details>


</details>

<details>
<summary>Advanced: covers attribute prefix selector matching</summary>

#### covers attribute prefix selector matching _(slow)_

- covers attribute prefix selector matching
   - Expected: _renders_color("div[data-route^='/app'] { width: 12px; height: 8px; background-color: #0f5e9c; }", "<div data-route='/app/home'></div>", 0xFF0F5E9Cu32) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("covers attribute prefix selector matching")
expect(_renders_color("div[data-route^='/app'] { width: 12px; height: 8px; background-color: #0f5e9c; }", "<div data-route='/app/home'></div>", 0xFF0F5E9Cu32)).to_equal(true)
```

</details>


</details>

<details>
<summary>Advanced: covers attribute suffix selector matching</summary>

#### covers attribute suffix selector matching _(slow)_

- covers attribute suffix selector matching
   - Expected: _renders_color("div[data-route$='/settings'] { width: 12px; height: 8px; background-color: #065f46; }", "<div data-route='/app/settings'></div>", 0xFF065F46u32) is true
   - Expected: _renders_color("div[data-route$='/settings'] { width: 12px; height: 8px; background-color: #065f46; }", "<div data-route='/app/settings/profile'></div>", 0xFF065F46u32) is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("covers attribute suffix selector matching")
expect(_renders_color("div[data-route$='/settings'] { width: 12px; height: 8px; background-color: #065f46; }", "<div data-route='/app/settings'></div>", 0xFF065F46u32)).to_equal(true)
expect(_renders_color("div[data-route$='/settings'] { width: 12px; height: 8px; background-color: #065f46; }", "<div data-route='/app/settings/profile'></div>", 0xFF065F46u32)).to_equal(false)
```

</details>


</details>

<details>
<summary>Advanced: covers attribute substring selector matching</summary>

#### covers attribute substring selector matching _(slow)_

- covers attribute substring selector matching
   - Expected: _renders_color("[data-tags*='beta'] { width: 12px; height: 8px; background-color: #9d174d; }", "<div data-tags='alpha-beta-release'></div>", 0xFF9D174Du32) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("covers attribute substring selector matching")
expect(_renders_color("[data-tags*='beta'] { width: 12px; height: 8px; background-color: #9d174d; }", "<div data-tags='alpha-beta-release'></div>", 0xFF9D174Du32)).to_equal(true)
```

</details>


</details>

<details>
<summary>Advanced: covers attribute whitespace token selector matching</summary>

#### covers attribute whitespace token selector matching _(slow)_

- covers attribute whitespace token selector matching
   - Expected: _renders_color("[data-flags~='selected'] { width: 12px; height: 8px; background-color: #7c2d12; }", "<div data-flags='primary selected visible'></div>", 0xFF7C2D12u32) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("covers attribute whitespace token selector matching")
expect(_renders_color("[data-flags~='selected'] { width: 12px; height: 8px; background-color: #7c2d12; }", "<div data-flags='primary selected visible'></div>", 0xFF7C2D12u32)).to_equal(true)
```

</details>


</details>

<details>
<summary>Advanced: covers attribute dash match selector matching</summary>

#### covers attribute dash match selector matching _(slow)_

- covers attribute dash match selector matching
   - Expected: _renders_color("div[lang|='en'] { width: 12px; height: 8px; background-color: #155e75; }", "<div lang='en-US'></div>", 0xFF155E75u32) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("covers attribute dash match selector matching")
expect(_renders_color("div[lang|='en'] { width: 12px; height: 8px; background-color: #155e75; }", "<div lang='en-US'></div>", 0xFF155E75u32)).to_equal(true)
```

</details>


</details>

<details>
<summary>Advanced: covers case insensitive attribute selector matching</summary>

#### covers case insensitive attribute selector matching _(slow)_

- covers case insensitive attribute selector matching
   - Expected: _renders_color("div[data-mode='dialog' i] { width: 12px; height: 8px; background-color: #4338ca; }", "<div data-mode='Dialog'></div>", 0xFF4338CAu32) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("covers case insensitive attribute selector matching")
expect(_renders_color("div[data-mode='dialog' i] { width: 12px; height: 8px; background-color: #4338ca; }", "<div data-mode='Dialog'></div>", 0xFF4338CAu32)).to_equal(true)
```

</details>


</details>

<details>
<summary>Advanced: covers explicit case sensitive attribute selector matching</summary>

#### covers explicit case sensitive attribute selector matching _(slow)_

- covers explicit case sensitive attribute selector matching
   - Expected: _renders_color("div[data-mode='Dialog' s] { width: 12px; height: 8px; background-color: #1d4ed8; }", "<div data-mode='Dialog'></div>", 0xFF1D4ED8u32) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("covers explicit case sensitive attribute selector matching")
expect(_renders_color("div[data-mode='Dialog' s] { width: 12px; height: 8px; background-color: #1d4ed8; }", "<div data-mode='Dialog'></div>", 0xFF1D4ED8u32)).to_equal(true)
```

</details>


</details>

#### CSS color and background basics

<details>
<summary>Advanced: covers six digit hex color</summary>

#### covers six digit hex color _(slow)_

- covers six digit hex color
   - Expected: _body_renders_color("background-color:#2563eb", 0xFF2563EBu32) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("covers six digit hex color")
expect(_body_renders_color("background-color:#2563eb", 0xFF2563EBu32)).to_equal(true)
```

</details>


</details>

<details>
<summary>Advanced: covers shorthand hex color</summary>

#### covers shorthand hex color _(slow)_

- covers shorthand hex color
   - Expected: _body_renders_color("background-color:#0f8", 0xFF00FF88u32) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("covers shorthand hex color")
expect(_body_renders_color("background-color:#0f8", 0xFF00FF88u32)).to_equal(true)
```

</details>


</details>

<details>
<summary>Advanced: covers legacy rgb function color</summary>

#### covers legacy rgb function color _(slow)_

- covers legacy rgb function color
   - Expected: _body_renders_color("background-color:rgb(5, 150, 105)", 0xFF059669u32) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("covers legacy rgb function color")
expect(_body_renders_color("background-color:rgb(5, 150, 105)", 0xFF059669u32)).to_equal(true)
```

</details>


</details>

<details>
<summary>Advanced: covers modern space separated rgb function color</summary>

#### covers modern space separated rgb function color _(slow)_

- covers modern space separated rgb function color
   - Expected: _body_renders_color("background-color:rgb(5 150 105)", 0xFF059669u32) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("covers modern space separated rgb function color")
expect(_body_renders_color("background-color:rgb(5 150 105)", 0xFF059669u32)).to_equal(true)
```

</details>


</details>

<details>
<summary>Advanced: covers rgba compositing over white</summary>

#### covers rgba compositing over white _(slow)_

- covers rgba compositing over white
   - Expected: _body_renders_color("background-color:rgba(0, 0, 0, 0.5)", 0xFF808080u32) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("covers rgba compositing over white")
expect(_body_renders_color("background-color:rgba(0, 0, 0, 0.5)", 0xFF808080u32)).to_equal(true)
```

</details>


</details>

<details>
<summary>Advanced: covers hsl function color</summary>

#### covers hsl function color _(slow)_

- covers hsl function color
   - Expected: _body_renders_color("background-color:hsl(120, 100%, 25%)", 0xFF008000u32) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("covers hsl function color")
expect(_body_renders_color("background-color:hsl(120, 100%, 25%)", 0xFF008000u32)).to_equal(true)
```

</details>


</details>

<details>
<summary>Advanced: covers named CSS color</summary>

#### covers named CSS color _(slow)_

- covers named CSS color
   - Expected: _body_renders_color("background-color:rebeccapurple", 0xFF663399u32) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("covers named CSS color")
expect(_body_renders_color("background-color:rebeccapurple", 0xFF663399u32)).to_equal(true)
```

</details>


</details>

<details>
<summary>Advanced: covers transparent compositing to white</summary>

#### covers transparent compositing to white _(slow)_

- covers transparent compositing to white
   - Expected: _body_renders_color("background-color:transparent", 0xFFFFFFFFu32) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("covers transparent compositing to white")
expect(_body_renders_color("background-color:transparent", 0xFFFFFFFFu32)).to_equal(true)
```

</details>


</details>

<details>
<summary>Advanced: covers function color background shorthand</summary>

#### covers function color background shorthand _(slow)_

- covers function color background shorthand
   - Expected: _body_renders_color("background:rgb(5, 150, 105) no-repeat", 0xFF059669u32) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("covers function color background shorthand")
expect(_body_renders_color("background:rgb(5, 150, 105) no-repeat", 0xFF059669u32)).to_equal(true)
```

</details>


</details>

<details>
<summary>Advanced: covers color-first background shorthand</summary>

#### covers color-first background shorthand _(slow)_

- covers color-first background shorthand
   - Expected: _body_renders_color("background:rebeccapurple no-repeat", 0xFF663399u32) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("covers color-first background shorthand")
expect(_body_renders_color("background:rebeccapurple no-repeat", 0xFF663399u32)).to_equal(true)
```

</details>


</details>

<details>
<summary>Advanced: covers url background shorthand fallback color</summary>

#### covers url background shorthand fallback color _(slow)_

- covers url background shorthand fallback color
   - Expected: _body_renders_color("background:url(hero.png) #0f8 no-repeat", 0xFF00FF88u32) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("covers url background shorthand fallback color")
expect(_body_renders_color("background:url(hero.png) #0f8 no-repeat", 0xFF00FF88u32)).to_equal(true)
```

</details>


</details>

<details>
<summary>Advanced: covers CSS custom property fallback colors</summary>

#### covers CSS custom property fallback colors _(slow)_

- covers CSS custom property fallback colors
   - Expected: _renders_color(".card { width: 12px; height: 8px; background-color: var(--missing-panel, #2563eb); }", "<div class='card'></div>", 0xFF2563EBu32) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("covers CSS custom property fallback colors")
expect(_renders_color(".card { width: 12px; height: 8px; background-color: var(--missing-panel, #2563eb); }", "<div class='card'></div>", 0xFF2563EBu32)).to_equal(true)
```

</details>


</details>

<details>
<summary>Advanced: covers CSS custom property fallback colors in background shorthand</summary>

#### covers CSS custom property fallback colors in background shorthand _(slow)_

- covers CSS custom property fallback colors in background shorthand
   - Expected: _renders_color(".card { width: 12px; height: 8px; background: var(--missing-panel, #0891b2) no-repeat; }", "<div class='card'></div>", 0xFF0891B2u32) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("covers CSS custom property fallback colors in background shorthand")
expect(_renders_color(".card { width: 12px; height: 8px; background: var(--missing-panel, #0891b2) no-repeat; }", "<div class='card'></div>", 0xFF0891B2u32)).to_equal(true)
```

</details>


</details>

<details>
<summary>Advanced: covers later background-color overriding shorthand</summary>

#### covers later background-color overriding shorthand _(slow)_

- covers later background-color overriding shorthand
   - Expected: _body_renders_color("background:#0f8; background-color:rebeccapurple", 0xFF663399u32) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("covers later background-color overriding shorthand")
expect(_body_renders_color("background:#0f8; background-color:rebeccapurple", 0xFF663399u32)).to_equal(true)
```

</details>


</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/feature/web_platform/css/selector_color_subset_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering WPT-derived CSS selector and color subset.
- WPT-derived CSS selector and color subset

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 57 |
| Active scenarios | 57 |
| Slow scenarios | 57 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-FEATURE`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `84ad8e35954e1c413fad36962cb7526e6e81ac97125569c135ae51e396285a4a`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `84ad8e35954e1c413fad36962cb7526e6e81ac97125569c135ae51e396285a4a`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `84ad8e35954e1c413fad36962cb7526e6e81ac97125569c135ae51e396285a4a`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/feature/web_platform/css/selector_color_subset_spec.spl
mirror: doc/06_spec/feature/web_platform/css/selector_color_subset_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/feature/web_platform/css/selector_color_subset_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/feature/web_platform/css/selector_color_subset_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, assumptions/preconditions, primary workflow, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/feature/web_platform/css/selector_color_subset_spec.spl:45:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'covers type selector matching' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/feature/web_platform/css/selector_color_subset_spec.spl:50:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'covers universal selector matching' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/feature/web_platform/css/selector_color_subset_spec.spl:55:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'covers class selector matching' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
