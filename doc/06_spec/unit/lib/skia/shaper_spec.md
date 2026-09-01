# Shaper Specification

> Tests covering script_of: Latin range, script_of: Hebrew range, script_of: Arabic range, script_of: CJK range, script_is_rtl, feature_tag, FallbackChain, Shaper, ascii_to_codepoints, shaper_shape: empty text, shaper_shape: ASCII Latin text, shaper_shape: mixed Latin + Arabic, shaper_shape: Arabic-only joining forms, shaper_shape: Devanagari reph classification, shaper_shape: glyph count matches codepoint count (no ligatures), shaper_shape: advances from font size when no OtFont, classify_thai_char, classify_myanmar_char, classify_khmer_char, classify_tibetan_char, classify_hangul_char, classify_hebrew_char, classify_mongolian_char.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 58 | 58 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Shaper Specification

## Scenarios

### script_of: Latin range

#### ASCII 'A' (0x0041) is Latin

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- ASCII 'A' (0x0041) is Latin


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("ASCII 'A' (0x0041) is Latin")
val cp = 65 as u32
val s = script_of(cp)
expect s to_equal Script.Latin
```

</details>

#### ASCII boundary 0x007F is Latin

- ASCII boundary 0x007F is Latin


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("ASCII boundary 0x007F is Latin")
val cp = 127 as u32
val s = script_of(cp)
expect s to_equal Script.Latin
```

</details>

### script_of: Hebrew range

#### Hebrew alef 0x05D0 (1488) is Hebrew

- Hebrew alef 0x05D0 (1488) is Hebrew


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("Hebrew alef 0x05D0 (1488) is Hebrew")
val cp = 1488 as u32
val s = script_of(cp)
expect s to_equal Script.Hebrew
```

</details>

### script_of: Arabic range

#### Arabic letter 0x0628 (1576) is Arabic

- Arabic letter 0x0628 (1576) is Arabic


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("Arabic letter 0x0628 (1576) is Arabic")
val cp = 1576 as u32
val s = script_of(cp)
expect s to_equal Script.Arabic
```

</details>

### script_of: CJK range

#### CJK 0x4E2D (19997) is CJK

- CJK 0x4E2D (19997) is CJK


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("CJK 0x4E2D (19997) is CJK")
val cp = 19997 as u32
val s = script_of(cp)
expect s to_equal Script.CJK
```

</details>

### script_is_rtl

#### Arabic is RTL

- Arabic is RTL


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("Arabic is RTL")
val r = script_is_rtl(Script.Arabic)
expect r to_equal true
```

</details>

#### Hebrew is RTL

- Hebrew is RTL


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("Hebrew is RTL")
val r = script_is_rtl(Script.Hebrew)
expect r to_equal true
```

</details>

#### Latin is not RTL

- Latin is not RTL


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("Latin is not RTL")
val r = script_is_rtl(Script.Latin)
expect r to_equal false
```

</details>

### feature_tag

#### Kerning tag is kern

- Kerning tag is kern


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("Kerning tag is kern")
val t = feature_tag(OpenTypeFeature.Kerning)
expect t to_equal "kern"
```

</details>

#### Ligatures tag is liga

- Ligatures tag is liga


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("Ligatures tag is liga")
val t = feature_tag(OpenTypeFeature.Ligatures)
expect t to_equal "liga"
```

</details>

#### SmallCaps tag is smcp

- SmallCaps tag is smcp


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("SmallCaps tag is smcp")
val t = feature_tag(OpenTypeFeature.SmallCaps)
expect t to_equal "smcp"
```

</details>

### FallbackChain

#### new stores primary font

- new stores primary font


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("new stores primary font")
val font = sk_font_default()
val chain = fallback_chain_new(font)
expect chain.primary.size to_equal 12.0
```

</details>

#### system_default_chain returns a chain with 12pt primary

- system_default_chain returns a chain with 12pt primary


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("system_default_chain returns a chain with 12pt primary")
val chain = system_default_chain()
expect chain.primary.size to_equal 12.0
```

</details>

#### returns primary font for Latin script

- returns primary font for Latin script


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns primary font for Latin script")
val primary = sk_font_new(sk_typeface_from_name("Primary Sans", sk_font_style_normal()), 12.0)
val arabic = sk_font_new(sk_typeface_from_name("Noto Sans Arabic", sk_font_style_normal()), 12.0)
val chain = fallback_chain_add(fallback_chain_new(primary), arabic)
val selected = fallback_chain_font_for_script(chain, Script.Latin)
expect selected.typeface.family_name to_equal "Primary Sans"
```

</details>

#### prefers script-named fallback font for Arabic

- prefers script-named fallback font for Arabic


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("prefers script-named fallback font for Arabic")
val primary = sk_font_new(sk_typeface_from_name("Primary Sans", sk_font_style_normal()), 12.0)
val arabic = sk_font_new(sk_typeface_from_name("Noto Sans Arabic", sk_font_style_normal()), 12.0)
val hebrew = sk_font_new(sk_typeface_from_name("Noto Sans Hebrew", sk_font_style_normal()), 12.0)
val chain = fallback_chain_add(fallback_chain_add(fallback_chain_new(primary), hebrew), arabic)
val selected = fallback_chain_font_for_script(chain, Script.Arabic)
expect selected.typeface.family_name to_equal "Noto Sans Arabic"
```

</details>

#### falls back to first fallback when no script-specific match exists

- falls back to first fallback when no script-specific match exists


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("falls back to first fallback when no script-specific match exists")
val primary = sk_font_new(sk_typeface_from_name("Primary Sans", sk_font_style_normal()), 12.0)
val fallback = sk_font_new(sk_typeface_from_name("Fallback Sans", sk_font_style_normal()), 12.0)
val chain = fallback_chain_add(fallback_chain_new(primary), fallback)
val selected = fallback_chain_font_for_script(chain, Script.CJK)
expect selected.typeface.family_name to_equal "Fallback Sans"
```

</details>

#### prefers attached fallback font when it alone covers the run

- prefers attached fallback font when it alone covers the run


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("prefers attached fallback font when it alone covers the run")
val demo = load_font("src/compiler_rust/vendor/ttf-parser/tests/fonts/demo.ttf")
expect (demo != nil) to_equal true
val handle = demo as std.nogc_sync_mut.io.font_ffi.FontHandle
val primary = sk_font_new(sk_typeface_from_name("Primary Sans", sk_font_style_normal()), 12.0)
val attached = sk_font_new(
    sk_typeface_from_attached_font("Demo Latin", sk_font_style_normal(), handle.path, handle.handle),
    12.0
)
val chain = fallback_chain_add(fallback_chain_new(primary), attached)
val cps: [u32] = [65 as u32]
val selected = fallback_chain_font_for_run(chain, Script.Latin, cps, 0, cps.len())
expect selected.typeface.family_name to_equal "Demo Latin"
free_font(handle)
```

</details>

#### falls back to heuristic script match when no attached font covers the run

- falls back to heuristic script match when no attached font covers the run


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("falls back to heuristic script match when no attached font covers the run")
val demo = load_font("src/compiler_rust/vendor/ttf-parser/tests/fonts/demo.ttf")
expect (demo != nil) to_equal true
val handle = demo as std.nogc_sync_mut.io.font_ffi.FontHandle
val primary = sk_font_new(
    sk_typeface_from_attached_font("Demo Latin", sk_font_style_normal(), handle.path, handle.handle),
    12.0
)
val cjk = sk_font_new(sk_typeface_from_name("Noto Sans CJK", sk_font_style_normal()), 12.0)
val chain = fallback_chain_add(fallback_chain_new(primary), cjk)
val cps: [u32] = [19997 as u32]
val selected = fallback_chain_font_for_run(chain, Script.CJK, cps, 0, cps.len())
expect selected.typeface.family_name to_equal "Noto Sans CJK"
free_font(handle)
```

</details>

### Shaper

#### shaper_new stores fallback chain

- shaper_new stores fallback chain


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("shaper_new stores fallback chain")
val chain = system_default_chain()
val shaper = shaper_new(chain)
expect shaper.fallback.primary.size to_equal 12.0
```

</details>

### ascii_to_codepoints

#### hello produces 5 codepoints

- hello produces 5 codepoints


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("hello produces 5 codepoints")
val cps = ascii_to_codepoints("hello")
expect cps.len() to_equal 5
```

</details>

#### first codepoint of hello is 104 (h)

- first codepoint of hello is 104 (h)


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("first codepoint of hello is 104 (h)")
val cps = ascii_to_codepoints("hello")
val first = cps[0]
expect first to_equal 104 as u32
```

</details>

### shaper_shape: empty text

#### empty codepoint list produces empty run list

- empty codepoint list produces empty run list


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("empty codepoint list produces empty run list")
val chain = system_default_chain()
val shaper = shaper_new(chain)
val runs = shaper_shape(shaper, [], sk_font_default(), 0.0, 0.0)
expect runs.len() to_equal 0
```

</details>

### shaper_shape: ASCII Latin text

#### ASCII 'hi' produces a single Latin run

- ASCII 'hi' produces a single Latin run


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("ASCII 'hi' produces a single Latin run")
val chain = system_default_chain()
val shaper = shaper_new(chain)
val cps = ascii_to_codepoints("hi")
val runs = shaper_shape(shaper, cps, sk_font_default(), 0.0, 0.0)
expect runs.len() to_equal 1
```

</details>

#### Latin run has correct script

- Latin run has correct script


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("Latin run has correct script")
val chain = system_default_chain()
val shaper = shaper_new(chain)
val cps = ascii_to_codepoints("hi")
val runs = shaper_shape(shaper, cps, sk_font_default(), 0.0, 0.0)
val run = runs[0]
expect run.script to_equal Script.Latin
```

</details>

#### Latin glyph ids match codepoints (identity mapping without OtFont)

- Latin glyph ids match codepoints (identity mapping without OtFont)


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("Latin glyph ids match codepoints (identity mapping without OtFont)")
val chain = system_default_chain()
val shaper = shaper_new(chain)
# 'A' = 65, 'B' = 66
val cps: [u32] = [65 as u32, 66 as u32]
val runs = shaper_shape(shaper, cps, sk_font_default(), 0.0, 0.0)
val run = runs[0]
val gid0 = run.glyph_ids[0]
val gid1 = run.glyph_ids[1]
expect gid0 to_equal 65 as u32
expect gid1 to_equal 66 as u32
```

</details>

### shaper_shape: mixed Latin + Arabic

#### mixed Latin then Arabic codepoints produces 2 runs

- mixed Latin then Arabic codepoints produces 2 runs


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("mixed Latin then Arabic codepoints produces 2 runs")
val chain = system_default_chain()
val shaper = shaper_new(chain)
# 'A'=65 (Latin), Arabic ba=1576
val cps: [u32] = [65 as u32, 1576 as u32]
val runs = shaper_shape(shaper, cps, sk_font_default(), 0.0, 0.0)
expect runs.len() to_equal 2
```

</details>

#### first run of mixed text is Latin

- first run of mixed text is Latin


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("first run of mixed text is Latin")
val chain = system_default_chain()
val shaper = shaper_new(chain)
val cps: [u32] = [65 as u32, 1576 as u32]
val runs = shaper_shape(shaper, cps, sk_font_default(), 0.0, 0.0)
val first_run = runs[0]
expect first_run.script to_equal Script.Latin
```

</details>

#### second run of mixed text is Arabic

- second run of mixed text is Arabic


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("second run of mixed text is Arabic")
val chain = system_default_chain()
val shaper = shaper_new(chain)
val cps: [u32] = [65 as u32, 1576 as u32]
val runs = shaper_shape(shaper, cps, sk_font_default(), 0.0, 0.0)
val second_run = runs[1]
expect second_run.script to_equal Script.Arabic
```

</details>

### shaper_shape: Arabic-only joining forms

#### Arabic run is RTL

- Arabic run is RTL


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("Arabic run is RTL")
val chain = system_default_chain()
val shaper = shaper_new(chain)
# Arabic: alef=1575, ba=1576, jim=1580
val cps: [u32] = [1575 as u32, 1576 as u32, 1580 as u32]
val runs = shaper_shape(shaper, cps, sk_font_default(), 0.0, 0.0)
val run = runs[0]
expect run.is_rtl to_equal true
```

</details>

#### Arabic sequence produces exactly 1 run

- Arabic sequence produces exactly 1 run


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("Arabic sequence produces exactly 1 run")
val chain = system_default_chain()
val shaper = shaper_new(chain)
val cps: [u32] = [1575 as u32, 1576 as u32, 1580 as u32]
val runs = shaper_shape(shaper, cps, sk_font_default(), 0.0, 0.0)
expect runs.len() to_equal 1
```

</details>

#### Arabic middle letter classified as Medial or Final (joining form set)

- Arabic middle letter classified as Medial or Final (joining form set)


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("Arabic middle letter classified as Medial or Final (joining form set)")
# ba (1576) between two joiners: alef (1575, right-joining only) on left, jim (1580) on right
# alef can join left (to ba on its right), ba can join right (to jim on its right)
# ba: has_left = alef joins to ba's left neighbor? alef is right-joining only so arabic_can_join_left(1575)=false
# ba: has_right = jim (1580) arabic_can_join_right(1580)=true (in 1576-1594 range)
# So ba gets Initial form
val cps: [u32] = [1575 as u32, 1576 as u32, 1580 as u32]
val form = arabic_join_form(cps, 1)
expect form to_equal ArabicJoinForm.Initial
```

</details>

#### isolated Arabic letter gets Isolated join form

- isolated Arabic letter gets Isolated join form


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("isolated Arabic letter gets Isolated join form")
val cps: [u32] = [1575 as u32]
val form = arabic_join_form(cps, 0)
expect form to_equal ArabicJoinForm.Isolated
```

</details>

### shaper_shape: Devanagari reph classification

#### Devanagari ra (2352) is classified as Reph

- Devanagari ra (2352) is classified as Reph


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("Devanagari ra (2352) is classified as Reph")
val cls = devanagari_classify(2352 as u32)
expect cls to_equal IndicClass.Reph
```

</details>

#### Devanagari virama (2381) is classified as Halant

- Devanagari virama (2381) is classified as Halant


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("Devanagari virama (2381) is classified as Halant")
val cls = devanagari_classify(2381 as u32)
expect cls to_equal IndicClass.Halant
```

</details>

#### Devanagari matra (2366) is classified as Matra

- Devanagari matra (2366) is classified as Matra


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("Devanagari matra (2366) is classified as Matra")
val cls = devanagari_classify(2366 as u32)
expect cls to_equal IndicClass.Matra
```

</details>

#### Devanagari run produces 1 run for Devanagari-only codepoints

- Devanagari run produces 1 run for Devanagari-only codepoints


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("Devanagari run produces 1 run for Devanagari-only codepoints")
val chain = system_default_chain()
val shaper = shaper_new(chain)
# Devanagari: ka=2325, virama=2381, ra=2352
val cps: [u32] = [2325 as u32, 2381 as u32, 2352 as u32]
val runs = shaper_shape(shaper, cps, sk_font_default(), 0.0, 0.0)
expect runs.len() to_equal 1
```

</details>

#### Devanagari run has Devanagari script

- Devanagari run has Devanagari script


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("Devanagari run has Devanagari script")
val chain = system_default_chain()
val shaper = shaper_new(chain)
val cps: [u32] = [2325 as u32, 2381 as u32, 2352 as u32]
val runs = shaper_shape(shaper, cps, sk_font_default(), 0.0, 0.0)
val run = runs[0]
expect run.script to_equal Script.Devanagari
```

</details>

#### leading ra + halant is reordered after the first base consonant

- leading ra + halant is reordered after the first base consonant


<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("leading ra + halant is reordered after the first base consonant")
val chain = system_default_chain()
val shaper = shaper_new(chain)
# ra + halant + ka
val cps: [u32] = [2352 as u32, 2381 as u32, 2325 as u32]
val runs = shaper_shape(shaper, cps, sk_font_default(), 0.0, 0.0)
val run = runs[0]
expect run.glyphs.len() to_equal 3
expect run.glyphs[0].indic_class to_equal IndicClass.Normal
expect run.glyphs[1].indic_class to_equal IndicClass.Reph
expect run.glyphs[2].indic_class to_equal IndicClass.Halant
expect run.glyphs[1].x_advance to_equal 0.0
expect run.glyphs[2].x_advance to_equal 0.0
expect run.positions[1].x to_equal run.positions[0].x + run.glyphs[0].x_advance
expect run.positions[2].x to_equal run.positions[1].x
```

</details>

### shaper_shape: glyph count matches codepoint count (no ligatures)

#### 3 ASCII codepoints produce 3 glyph ids

- 3 ASCII codepoints produce 3 glyph ids


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("3 ASCII codepoints produce 3 glyph ids")
val chain = system_default_chain()
val shaper = shaper_new(chain)
val cps: [u32] = [72 as u32, 105 as u32, 33 as u32]
val runs = shaper_shape(shaper, cps, sk_font_default(), 0.0, 0.0)
val run = runs[0]
expect run.glyph_ids.len() to_equal 3
```

</details>

#### positions count matches glyph count

- positions count matches glyph count


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("positions count matches glyph count")
val chain = system_default_chain()
val shaper = shaper_new(chain)
val cps: [u32] = [72 as u32, 105 as u32, 33 as u32]
val runs = shaper_shape(shaper, cps, sk_font_default(), 0.0, 0.0)
val run = runs[0]
expect run.positions.len() to_equal run.glyph_ids.len()
```

</details>

### shaper_shape: advances from font size when no OtFont

#### positions are monotonically increasing for LTR Latin

- positions are monotonically increasing for LTR Latin


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("positions are monotonically increasing for LTR Latin")
val chain = system_default_chain()
val shaper = shaper_new(chain)
val cps: [u32] = [65 as u32, 66 as u32, 67 as u32]
val runs = shaper_shape(shaper, cps, sk_font_default(), 0.0, 0.0)
val run = runs[0]
val x0 = run.positions[0].x
val x1 = run.positions[1].x
val x2 = run.positions[2].x
expect x1 to_be_greater_than x0
expect x2 to_be_greater_than x1
```

</details>

#### first position x is start_x

- first position x is start_x


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("first position x is start_x")
val chain = system_default_chain()
val shaper = shaper_new(chain)
val cps: [u32] = [65 as u32, 66 as u32]
val runs = shaper_shape(shaper, cps, sk_font_default(), 10.0, 5.0)
val run = runs[0]
expect run.positions[0].x to_equal 10.0
```

</details>

### classify_thai_char

#### Thai ko kai U+0E01 is Consonant

- Thai ko kai U+0E01 is Consonant


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("Thai ko kai U+0E01 is Consonant")
val c = classify_thai_char(0x0E01)
expect c to_equal ThaiClass.Consonant
```

</details>

#### Thai sara a U+0E30 is Vowel

- Thai sara a U+0E30 is Vowel


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("Thai sara a U+0E30 is Vowel")
val c = classify_thai_char(0x0E30)
expect c to_equal ThaiClass.Vowel
```

</details>

#### Thai mai ek U+0E48 is ToneMark

- Thai mai ek U+0E48 is ToneMark


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("Thai mai ek U+0E48 is ToneMark")
val c = classify_thai_char(0x0E48)
expect c to_equal ThaiClass.ToneMark
```

</details>

### classify_myanmar_char

#### Myanmar ka U+1000 is Consonant

- Myanmar ka U+1000 is Consonant


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("Myanmar ka U+1000 is Consonant")
val c = classify_myanmar_char(0x1000)
expect c to_equal MyanmarClass.Consonant
```

</details>

#### Myanmar asat/virama U+1039 is Virama

- Myanmar asat/virama U+1039 is Virama


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("Myanmar asat/virama U+1039 is Virama")
val c = classify_myanmar_char(0x1039)
expect c to_equal MyanmarClass.Virama
```

</details>

### classify_khmer_char

#### Khmer ka U+1780 is Consonant

- Khmer ka U+1780 is Consonant


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("Khmer ka U+1780 is Consonant")
val c = classify_khmer_char(0x1780)
expect c to_equal KhmerClass.Consonant
```

</details>

#### Khmer coeng U+17D2 is Coeng

- Khmer coeng U+17D2 is Coeng


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("Khmer coeng U+17D2 is Coeng")
val c = classify_khmer_char(0x17D2)
expect c to_equal KhmerClass.Coeng
```

</details>

### classify_tibetan_char

#### Tibetan ka U+0F40 is Consonant

- Tibetan ka U+0F40 is Consonant


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("Tibetan ka U+0F40 is Consonant")
val c = classify_tibetan_char(0x0F40)
expect c to_equal TibetanClass.Consonant
```

</details>

#### Tibetan subjoined ka U+0F90 is Subjoined

- Tibetan subjoined ka U+0F90 is Subjoined


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("Tibetan subjoined ka U+0F90 is Subjoined")
val c = classify_tibetan_char(0x0F90)
expect c to_equal TibetanClass.Subjoined
```

</details>

### classify_hangul_char

#### Hangul leading jamo U+1100 is LeadingJamo

- Hangul leading jamo U+1100 is LeadingJamo


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("Hangul leading jamo U+1100 is LeadingJamo")
val c = classify_hangul_char(0x1100)
expect c to_equal HangulClass.LeadingJamo
```

</details>

#### Hangul precomposed syllable U+AC00 is PrecomposedSyllable

- Hangul precomposed syllable U+AC00 is PrecomposedSyllable


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("Hangul precomposed syllable U+AC00 is PrecomposedSyllable")
val c = classify_hangul_char(0xAC00)
expect c to_equal HangulClass.PrecomposedSyllable
```

</details>

### classify_hebrew_char

#### Hebrew alef U+05D0 is Consonant

- Hebrew alef U+05D0 is Consonant


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("Hebrew alef U+05D0 is Consonant")
val c = classify_hebrew_char(0x05D0)
expect c to_equal HebrewClass.Consonant
```

</details>

#### Hebrew final kaf U+05DA is FinalConsonant

- Hebrew final kaf U+05DA is FinalConsonant


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("Hebrew final kaf U+05DA is FinalConsonant")
val c = classify_hebrew_char(0x05DA)
expect c to_equal HebrewClass.FinalConsonant
```

</details>

#### Hebrew patah U+05B7 is Point

- Hebrew patah U+05B7 is Point


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("Hebrew patah U+05B7 is Point")
val c = classify_hebrew_char(0x05B7)
expect c to_equal HebrewClass.Point
```

</details>

### classify_mongolian_char

#### Mongolian consonant U+1820 is Consonant

- Mongolian consonant U+1820 is Consonant


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("Mongolian consonant U+1820 is Consonant")
val c = classify_mongolian_char(0x1820)
expect c to_equal MongolianClass.Consonant
```

</details>

#### Mongolian FVS1 U+180B is FormatControl

- Mongolian FVS1 U+180B is FormatControl


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("Mongolian FVS1 U+180B is FormatControl")
val c = classify_mongolian_char(0x180B)
expect c to_equal MongolianClass.FormatControl
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/unit/lib/skia/shaper_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering script_of: Latin range, script_of: Hebrew range, script_of: Arabic range, script_of: CJK range, script_is_rtl, feature_tag, FallbackChain, Shaper, ascii_to_codepoints, shaper_shape: empty text, shaper_shape: ASCII Latin text, shaper_shape: mixed Latin + Arabic, shaper_shape: Arabic-only joining forms, shaper_shape: Devanagari reph classification, shaper_shape: glyph count matches codepoint count (no ligatures), shaper_shape: advances from font size when no OtFont, classify_thai_char, classify_myanmar_char, classify_khmer_char, classify_tibetan_char, classify_hangul_char, classify_hebrew_char, classify_mongolian_char.
- script_of: Latin range
- script_of: Hebrew range
- script_of: Arabic range
- script_of: CJK range
- script_is_rtl
- feature_tag
- FallbackChain
- Shaper
- ascii_to_codepoints
- shaper_shape: empty text
- shaper_shape: ASCII Latin text
- shaper_shape: mixed Latin + Arabic
- shaper_shape: Arabic-only joining forms
- shaper_shape: Devanagari reph classification
- shaper_shape: glyph count matches codepoint count (no ligatures)
- shaper_shape: advances from font size when no OtFont
- classify_thai_char
- classify_myanmar_char
- classify_khmer_char
- classify_tibetan_char
- classify_hangul_char
- classify_hebrew_char
- classify_mongolian_char

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 58 |
| Active scenarios | 58 |
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

- Canonical SPipe generation for source `8bf5086575a06818b62465f3f0babf1137999a39e80f1441ab30371e426511ed`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `8bf5086575a06818b62465f3f0babf1137999a39e80f1441ab30371e426511ed`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `8bf5086575a06818b62465f3f0babf1137999a39e80f1441ab30371e426511ed`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/unit/lib/skia/shaper_spec.spl
mirror: doc/06_spec/unit/lib/skia/shaper_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/unit/lib/skia/shaper_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/unit/lib/skia/shaper_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/unit/lib/skia/shaper_spec.spl:19:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'ASCII 'A' (0x0041) is Latin' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/lib/skia/shaper_spec.spl:26:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'ASCII boundary 0x007F is Latin' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/lib/skia/shaper_spec.spl:34:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'Hebrew alef 0x05D0 (1488) is Hebrew' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
