# Shaper Specification

> Tests covering script_of: Latin range, Common and Inherited script resolution, script_of: Bengali range, script_of: Hebrew range, script_of: Arabic range, script_of: Cyrillic range, script_of: CJK range, selected font corpus shaping metadata, script_is_rtl, feature_tag, FallbackChain, Shaper, ascii_to_codepoints, shaper_shape: empty text, shaper_shape: ASCII Latin text, shaper_shape: mixed Latin + Arabic, shaper_shape: provisional Arabic joining classification, shaper_shape: provisional Devanagari reph classification, shaper metadata, shaper_shape: unbound ASCII identity diagnostic, shaper_shape: fallback placement estimate without OtFont, classify_thai_char, classify_myanmar_char, classify_khmer_char, classify_tibetan_char, classify_hangul_char, classify_hebrew_char, classify_mongolian_char.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 83 | 83 | 0 | 0 |

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
# @req REQ-SSPEC-LIB
step("ASCII 'A' (0x0041) is Latin")
val cp = 65 as u32
val s = script_of(cp)
expect s to_equal Script.Latin
```

</details>

#### ASCII non-letters are Common

- ASCII non-letters are Common


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("ASCII non-letters are Common")
val cp = 127 as u32
val s = script_of(cp)
expect s to_equal Script.Common
expect script_of(32u32) to_equal Script.Common
expect script_of(48u32) to_equal Script.Common
```

</details>

#### selected Latin-1 witnesses stay in one script

- selected Latin-1 witnesses stay in one script


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("selected Latin-1 witnesses stay in one script")
expect script_of(241 as u32) to_equal Script.Latin
expect script_of(231 as u32) to_equal Script.Latin
expect script_of(234 as u32) to_equal Script.Latin
```

</details>

### Common and Inherited script resolution

#### classifies combining marks and join controls without inventing a strong script

- classifies combining marks and join controls without inventing a strong script


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("classifies combining marks and join controls without inventing a strong script")
expect script_of(769u32) to_equal Script.Inherited
expect script_of(8205u32) to_equal Script.Common
```

</details>

#### attaches a trailing combining mark to the preceding strong script

- attaches a trailing combining mark to the preceding strong script


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("attaches a trailing combining mark to the preceding strong script")
val runs = shaper_shape(shaper_new(system_default_chain()), [65u32, 769u32], sk_font_default(), 0.0, 0.0)
expect runs.len() to_equal 1
expect runs[0].script to_equal Script.Latin
expect runs[0].glyphs.len() to_equal 2
```

</details>

#### attaches a leading combining mark to the following strong script

- attaches a leading combining mark to the following strong script


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("attaches a leading combining mark to the following strong script")
val runs = shaper_shape(shaper_new(system_default_chain()), [769u32, 1040u32], sk_font_default(), 0.0, 0.0)
expect runs.len() to_equal 1
expect runs[0].script to_equal Script.Cyrillic
expect runs[0].glyphs.len() to_equal 2
```

</details>

#### attaches a neutral between differing scripts to the preceding script

- attaches a neutral between differing scripts to the preceding script


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("attaches a neutral between differing scripts to the preceding script")
val runs = shaper_shape(shaper_new(system_default_chain()), [65u32, 8205u32, 1040u32], sk_font_default(), 0.0, 0.0)
expect runs.len() to_equal 2
expect runs[0].script to_equal Script.Latin
expect runs[0].glyphs.len() to_equal 2
expect runs[1].script to_equal Script.Cyrillic
expect runs[1].glyphs.len() to_equal 1
```

</details>

#### resolves leading trailing and between-script spaces

- resolves leading trailing and between-script spaces


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("resolves leading trailing and between-script spaces")
val leading = shaper_shape(shaper_new(system_default_chain()), [32u32, 1040u32], sk_font_default(), 0.0, 0.0)
expect leading.len() to_equal 1
expect leading[0].script to_equal Script.Cyrillic
val trailing = shaper_shape(shaper_new(system_default_chain()), [1576u32, 32u32], sk_font_default(), 0.0, 0.0)
expect trailing.len() to_equal 1
expect trailing[0].script to_equal Script.Arabic
val between = shaper_shape(shaper_new(system_default_chain()), [1040u32, 32u32, 2309u32], sk_font_default(), 0.0, 0.0)
expect between.len() to_equal 2
expect between[0].glyphs.len() to_equal 2
```

</details>

#### resolves a long neutral run without splitting

- resolves a long neutral run without splitting


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("resolves a long neutral run without splitting")
var codepoints: [u32] = [65u32]
var index: i64 = 0
while index < 256:
    codepoints.push(32u32)
    index = index + 1
codepoints.push(1040u32)
val runs = shaper_shape(shaper_new(system_default_chain()), codepoints, sk_font_default(), 0.0, 0.0)
expect runs.len() to_equal 2
expect runs[0].glyphs.len() to_equal 257
```

</details>

#### leaves an all-neutral run unresolved and invalid

- leaves an all-neutral run unresolved and invalid


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("leaves an all-neutral run unresolved and invalid")
val runs = shaper_shape(shaper_new(system_default_chain()), [769u32], sk_font_default(), 0.0, 0.0)
expect runs.len() to_equal 1
expect runs[0].script to_equal Script.Inherited
expect runs[0].glyph_indices_valid to_equal false
```

</details>

#### keeps the primary font for an unresolved Inherited run

- keeps the primary font for an unresolved Inherited run


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("keeps the primary font for an unresolved Inherited run")
val primary = sk_font_new(sk_typeface_from_name("Inherited Primary", sk_font_style_normal()), 12.0)
val fallback = sk_font_new(sk_typeface_from_name("Inherited Fallback", sk_font_style_normal()), 12.0)
val chain = fallback_chain_add(fallback_chain_new(primary), fallback)
expect fallback_chain_font_for_script(chain, Script.Inherited).typeface.family_name to_equal "Inherited Primary"
```

</details>

### script_of: Bengali range

#### rank-11 Bengali letters are identified without claiming shaping

- rank-11 Bengali letters are identified without claiming shaping


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("rank-11 Bengali letters are identified without claiming shaping")
expect script_of(2476 as u32) to_equal Script.Bengali
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
# @req REQ-SSPEC-LIB
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
# @req REQ-SSPEC-LIB
step("Arabic letter 0x0628 (1576) is Arabic")
val cp = 1576 as u32
val s = script_of(cp)
expect s to_equal Script.Arabic
```

</details>

#### Urdu Arabic Extended-A letter U+08A0 is Arabic

- Urdu Arabic Extended-A letter U+08A0 is Arabic


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("Urdu Arabic Extended-A letter U+08A0 is Arabic")
expect script_of(2208 as u32) to_equal Script.Arabic
```

</details>

### script_of: Cyrillic range

#### Russian ya U+044F is Cyrillic

- Russian ya U+044F is Cyrillic


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("Russian ya U+044F is Cyrillic")
expect script_of(1103 as u32) to_equal Script.Cyrillic
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
# @req REQ-SSPEC-LIB
step("CJK 0x4E2D (19997) is CJK")
val cp = 19997 as u32
val s = script_of(cp)
expect s to_equal Script.CJK
```

</details>

### selected font corpus shaping metadata

#### keeps exact direct-script witnesses in one stable run

- keeps exact direct-script witnesses in one stable run


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("keeps exact direct-script witnesses in one stable run")
_expect_direct_corpus("en", [69u32, 110u32, 103u32, 108u32, 105u32, 115u32, 104u32], Script.Latin)
_expect_direct_corpus("zh", [20013u32, 25991u32], Script.CJK)
_expect_direct_corpus("es", [69u32, 115u32, 112u32, 97u32, 241u32, 111u32, 108u32], Script.Latin)
_expect_direct_corpus("fr", [102u32, 114u32, 97u32, 110u32, 231u32, 97u32, 105u32, 115u32], Script.Latin)
_expect_direct_corpus("pt", [80u32, 111u32, 114u32, 116u32, 117u32, 103u32, 117u32, 234u32, 115u32], Script.Latin)
_expect_direct_corpus("ru", [1056u32, 1091u32, 1089u32, 1089u32, 1082u32, 1080u32, 1081u32], Script.Cyrillic)
_expect_direct_corpus("id", [73u32, 110u32, 100u32, 111u32, 110u32, 101u32, 115u32, 105u32, 97u32], Script.Latin)
_expect_direct_corpus("und", [128512u32], Script.Emoji)
```

</details>

#### exposes exact complex-script clusters while material stays invalid

- exposes exact complex-script clusters while material stays invalid


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("exposes exact complex-script clusters while material stays invalid")
_expect_complex_corpus("hi", [2361u32, 2367u32, 2344u32, 2381u32, 2342u32, 2368u32], Script.Devanagari, [0, 1, 2, 3, 4, 5])
_expect_complex_corpus("ar", [1575u32, 1604u32, 1593u32, 1585u32, 1576u32, 1610u32, 1577u32], Script.Arabic, [6, 5, 4, 3, 2, 1, 0])
_expect_complex_corpus("ur", [1575u32, 1585u32, 1583u32, 1608u32], Script.Arabic, [3, 2, 1, 0])
_expect_complex_corpus("bn", [2476u32, 2494u32, 2434u32, 2482u32, 2494u32], Script.Bengali, [0, 1, 2, 3, 4])
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
# @req REQ-SSPEC-LIB
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
# @req REQ-SSPEC-LIB
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
# @req REQ-SSPEC-LIB
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
# @req REQ-SSPEC-LIB
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
# @req REQ-SSPEC-LIB
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
# @req REQ-SSPEC-LIB
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
# @req REQ-SSPEC-LIB
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
# @req REQ-SSPEC-LIB
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
# @req REQ-SSPEC-LIB
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
# @req REQ-SSPEC-LIB
step("prefers script-named fallback font for Arabic")
val primary = sk_font_new(sk_typeface_from_name("Primary Sans", sk_font_style_normal()), 12.0)
val arabic = sk_font_new(sk_typeface_from_name("Noto Sans Arabic", sk_font_style_normal()), 12.0)
val hebrew = sk_font_new(sk_typeface_from_name("Noto Sans Hebrew", sk_font_style_normal()), 12.0)
val chain = fallback_chain_add(fallback_chain_add(fallback_chain_new(primary), hebrew), arabic)
val selected = fallback_chain_font_for_script(chain, Script.Arabic)
expect selected.typeface.family_name to_equal "Noto Sans Arabic"
```

</details>

#### prefers script-named fallback font for Cyrillic

- prefers script-named fallback font for Cyrillic


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("prefers script-named fallback font for Cyrillic")
val primary = sk_font_new(sk_typeface_from_name("Primary Sans", sk_font_style_normal()), 12.0)
val cyrillic = sk_font_new(sk_typeface_from_name("Noto Sans Cyrillic", sk_font_style_normal()), 12.0)
val chain = fallback_chain_add(fallback_chain_new(primary), cyrillic)
val selected = fallback_chain_font_for_script(chain, Script.Cyrillic)
expect selected.typeface.family_name to_equal "Noto Sans Cyrillic"
```

</details>

#### falls back to first fallback when no script-specific match exists

- falls back to first fallback when no script-specific match exists


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
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
# @req REQ-SSPEC-LIB
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
# @req REQ-SSPEC-LIB
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
# @req REQ-SSPEC-LIB
step("shaper_new stores fallback chain")
val chain = system_default_chain()
val shaper = shaper_new(chain)
expect shaper.fallback.primary.size to_equal 12.0
```

</details>

#### marks glyph indices valid only for a cmap bound to the selected face

- marks glyph indices valid only for a cmap bound to the selected face
   - Expected: handle.is_live() is true
   - Expected: runs[0].glyph_indices_valid is true
   - Expected: runs[0].substitution_complete is true
   - Expected: runs[0].positioning_complete is true
   - Expected: read_u16_be(parsed.unwrap().blob, find_table(parsed.unwrap(), 1751474532u32).unwrap().offset as i64 + 18) equals `2048u32`
   - Expected: runs[0].glyphs[0].x_advance equals `metrics.advance_width as f64 * 12.0 / 2048.0`
   - Expected: material.valid is true
   - Expected: shaped_run_to_font_glyph_run(incomplete).valid is false
   - Expected: material.face_id equals `handle.handle`
   - Expected: material.face_generation equals `handle.generation`
   - Expected: material.clusters equals `[0]`
   - Expected: shaped_run_to_font_glyph_run(malformed).valid is false
   - Expected: shaped_run_to_font_glyph_run(malformed).valid is false
   - Expected: shaped_run_to_font_glyph_run(malformed).valid is false
   - Expected: rejected.substitution_complete is false
   - Expected: rejected.positioning_complete is false
   - Expected: shaped_run_to_font_glyph_run(rejected).valid is false
   - Expected: handle.is_live() is false
   - Expected: get_line_height(handle, 12.0) equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 49 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("marks glyph indices valid only for a cmap bound to the selected face")
val path = "assets/fonts/google-fonts/apache/robotoslab/RobotoSlab[wght].ttf"
val loaded = load_font(path)
expect(loaded).to_not_be_nil()
val handle = loaded as std.nogc_sync_mut.io.font_ffi.FontHandle
expect(handle.is_live()).to_equal(true)
val parsed = parse_offset_table(rt_file_read_bytes(path))
expect(parsed).to_not_equal(None)
val font = sk_font_new(sk_typeface_from_attached_font("Roboto Slab", sk_font_style_normal(), path, handle.handle), 12.0)
val bound = shaper_with_ot_face(shaper_new(fallback_chain_new(font)), handle.handle, parsed.unwrap())
val runs = shaper_shape(bound, [65u32], font, 0.0, 0.0)
expect(runs[0].glyph_indices_valid).to_equal(true)
expect(runs[0].substitution_complete).to_equal(true)
expect(runs[0].positioning_complete).to_equal(true)
val hhea = find_table(parsed.unwrap(), 1751672161u32).unwrap()
val metric_count = read_u16_be(parsed.unwrap().blob, hhea.offset as i64 + 34)
val metrics = parse_hmtx(parsed.unwrap(), metric_count, runs[0].glyph_ids[0]).unwrap()
expect(read_u16_be(parsed.unwrap().blob, find_table(parsed.unwrap(), 1751474532u32).unwrap().offset as i64 + 18)).to_equal(2048u32)
expect(runs[0].glyphs[0].x_advance).to_equal(metrics.advance_width as f64 * 12.0 / 2048.0)
val material = shaped_run_to_font_glyph_run(runs[0])
expect(material.valid).to_equal(true)
var incomplete = runs[0]
incomplete.positioning_complete = false
expect(shaped_run_to_font_glyph_run(incomplete).valid).to_equal(false)
expect(material.face_id).to_equal(handle.handle)
expect(material.face_generation).to_equal(handle.generation)
expect(material.clusters).to_equal([0])
var malformed = runs[0]
malformed.positions = [SkPoint(x: 2147483648.0, y: 0.0)]
expect(shaped_run_to_font_glyph_run(malformed).valid).to_equal(false)
malformed.positions = [SkPoint(x: 0.0, y: 0.0)]
malformed.glyphs[0].glyph_id = malformed.glyph_ids[0] + 1u32
expect(shaped_run_to_font_glyph_run(malformed).valid).to_equal(false)
malformed.glyphs[0].glyph_id = malformed.glyph_ids[0]
malformed.glyphs[0].cluster = -1
expect(shaped_run_to_font_glyph_run(malformed).valid).to_equal(false)
var zero_upem = parsed.unwrap()
val head = find_table(zero_upem, 1751474532u32).unwrap()
zero_upem.blob[head.offset as i64 + 18] = 0u8
zero_upem.blob[head.offset as i64 + 19] = 0u8
val rejected = shaper_shape(shaper_with_ot_face(shaper_new(fallback_chain_new(font)), handle.handle, zero_upem), [65u32], font, 0.0, 0.0)[0]
expect(rejected.substitution_complete).to_equal(false)
expect(rejected.positioning_complete).to_equal(false)
expect(shaped_run_to_font_glyph_run(rejected).valid).to_equal(false)
free_font(handle)
expect(handle.is_live()).to_equal(false)
expect(get_line_height(handle, 12.0)).to_equal(0)
free_font(handle)
```

</details>

#### applies a requested feature through the selected OpenType plan

- applies a requested feature through the selected OpenType plan
   - Expected: run.glyph_indices_valid is true
   - Expected: run.substitution_complete is true
   - Expected: run.positioning_complete is true
   - Expected: shaped_run_to_font_glyph_run(run).valid is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("applies a requested feature through the selected OpenType plan")
val path = "assets/fonts/google-fonts/ofl/nunito/Nunito[wght].ttf"
val loaded = load_font(path)
expect(loaded).to_not_be_nil()
val handle = loaded as std.nogc_sync_mut.io.font_ffi.FontHandle
val parsed = parse_offset_table(rt_file_read_bytes(path))
expect(parsed).to_not_equal(None)
val font = sk_font_new(sk_typeface_from_attached_font("Nunito", sk_font_style_normal(), path, handle.handle), 12.0)
val bound = shaper_with_ot_face(shaper_with_features(shaper_new(fallback_chain_new(font)), [OpenTypeFeature.Kerning]), handle.handle, parsed.unwrap())
val run = shaper_shape(bound, [65u32], font, 0.0, 0.0)[0]
expect(run.glyph_indices_valid).to_equal(true)
expect(run.substitution_complete).to_equal(true)
expect(run.positioning_complete).to_equal(true)
expect(shaped_run_to_font_glyph_run(run).valid).to_equal(true)
free_font(handle)
```

</details>

#### matches the pinned HarfBuzz Arabic and Urdu default-instance oracles

- matches the pinned HarfBuzz Arabic and Urdu default-instance oracles


<details>
<summary>Executable SSpec</summary>

Runnable source: 56 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("matches the pinned HarfBuzz Arabic and Urdu default-instance oracles")
val path = "assets/fonts/google-fonts/ofl/notosansarabic/NotoSansArabic[wdth,wght].ttf"
val loaded = load_font(path)
expect(loaded).to_not_be_nil()
val handle = loaded as std.nogc_sync_mut.io.font_ffi.FontHandle
val parsed = parse_offset_table(rt_file_read_bytes(path))
expect(parsed).to_not_equal(None)
val font = sk_font_new(sk_typeface_from_attached_font("Noto Sans Arabic", sk_font_style_normal(), path, handle.handle), 32.0)
val bound = shaper_with_ot_face(shaper_new(fallback_chain_new(font)), handle.handle, parsed.unwrap())
val arabic_codepoints = [1575u32, 1604u32, 1593u32, 1585u32, 1576u32, 1610u32, 1577u32]
val arabic = shaper_shape_with_language(bound, arabic_codepoints, font, 0.0, 0.0, "ar")[0]
expect arabic.language to_equal "ar"
expect arabic.is_rtl to_equal true
expect arabic.glyph_indices_valid to_equal true
expect arabic.substitution_complete to_equal true
expect arabic.positioning_complete to_equal true
val arabic_ids = [288u32, 85u32, 319u32, 18u32, 317u32, 19u32, 31u32, 48u32, 72u32, 8u32]
val arabic_clusters = [6, 6, 5, 5, 4, 4, 3, 2, 1, 0]
val arabic_advances = [0.0, 15.552, 0.0, 11.936, 0.0, 8.608, 11.712, 16.672, 8.320, 7.616]
val arabic_offsets = [3.232, 0.0, 1.248, 0.0, 0.992, 0.0, -0.960, 0.0, 0.0, 0.0]
val arabic_y_offsets = [2.080, 0.0, -0.160, 0.0, -0.096, 0.0, 0.0, 0.0, 0.0, 0.0]
var oracle_index: i64 = 0
while oracle_index < arabic_ids.len():
    expect arabic.glyphs[oracle_index].glyph_id to_equal arabic_ids[oracle_index]
    expect arabic.glyphs[oracle_index].cluster to_equal arabic_clusters[oracle_index]
    expect arabic.glyphs[oracle_index].x_advance to_equal arabic_advances[oracle_index]
    expect arabic.glyphs[oracle_index].x_offset to_equal arabic_offsets[oracle_index]
    expect arabic.glyphs[oracle_index].y_offset to_equal arabic_y_offsets[oracle_index]
    expect arabic.positions[oracle_index].y to_equal -arabic_y_offsets[oracle_index]
    expect arabic.glyphs[oracle_index].join_form to_equal arabic_join_form(arabic_codepoints, arabic.glyphs[oracle_index].source_index)
    oracle_index = oracle_index + 1
expect shaped_run_to_font_glyph_run(arabic).valid to_equal true
val urdu = shaper_shape_with_language(bound, [1575u32, 1585u32, 1583u32, 1608u32], font, 0.0, 0.0, "ur")[0]
expect urdu.language to_equal "ur"
expect urdu.glyph_indices_valid to_equal true
expect urdu.substitution_complete to_equal true
expect urdu.positioning_complete to_equal true
val urdu_ids = [98u32, 28u32, 30u32, 8u32]
val urdu_clusters = [3, 2, 1, 0]
val urdu_advances = [14.304, 15.264, 10.784, 7.616]
val urdu_offsets = [0.0, 0.0, -0.960, 0.0]
oracle_index = 0
while oracle_index < urdu_ids.len():
    expect urdu.glyphs[oracle_index].glyph_id to_equal urdu_ids[oracle_index]
    expect urdu.glyphs[oracle_index].cluster to_equal urdu_clusters[oracle_index]
    expect urdu.glyphs[oracle_index].x_advance to_equal urdu_advances[oracle_index]
    expect urdu.glyphs[oracle_index].x_offset to_equal urdu_offsets[oracle_index]
    expect urdu.glyphs[oracle_index].y_offset to_equal 0.0
    oracle_index = oracle_index + 1
expect shaped_run_to_font_glyph_run(urdu).valid to_equal true
val marked = shaper_shape_with_language(bound, [1576u32, 1614u32], font, 0.0, 0.0, "ar")[0]
expect marked.substitution_complete to_equal false
expect marked.positioning_complete to_equal false
expect shaped_run_to_font_glyph_run(marked).valid to_equal false
free_font(handle)
```

</details>

#### keeps GSUB completion independent and rolls back when GPOS is invalid

- keeps GSUB completion independent and rolls back when GPOS is invalid


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("keeps GSUB completion independent and rolls back when GPOS is invalid")
val path = "assets/fonts/google-fonts/ofl/notosansarabic/NotoSansArabic[wdth,wght].ttf"
val handle = load_font(path) as std.nogc_sync_mut.io.font_ffi.FontHandle
var parsed = parse_offset_table(rt_file_read_bytes(path)).unwrap()
val codepoints = [1575u32, 1604u32, 1593u32, 1585u32, 1576u32, 1610u32, 1577u32]
val gpos = find_table(parsed, 1196445523u32).unwrap()
parsed.blob[gpos.offset as i64 + 1] = 0u8
val font = sk_font_new(sk_typeface_from_attached_font("Noto Sans Arabic", sk_font_style_normal(), path, handle.handle), 32.0)
val run = shaper_shape_with_language(shaper_with_ot_face(shaper_new(fallback_chain_new(font)), handle.handle, parsed), codepoints, font, 0.0, 0.0, "ar")[0]
expect run.substitution_complete to_equal true
expect run.positioning_complete to_equal false
expect run.glyph_ids to_equal [cmap_glyph_id(parsed, 1577u32), cmap_glyph_id(parsed, 1610u32), cmap_glyph_id(parsed, 1576u32), cmap_glyph_id(parsed, 1585u32), cmap_glyph_id(parsed, 1593u32), cmap_glyph_id(parsed, 1604u32), cmap_glyph_id(parsed, 1575u32)]
expect shaped_run_to_font_glyph_run(run).valid to_equal false
free_font(handle)
```

</details>

#### accepts one bound emoji witness but rejects an unshaped emoji sequence

- accepts one bound emoji witness but rejects an unshaped emoji sequence


<details>
<summary>Executable SSpec</summary>

Runnable source: 32 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("accepts one bound emoji witness but rejects an unshaped emoji sequence")
val path = "assets/fonts/google-fonts/ofl/notoemoji/NotoEmoji[wght].ttf"
val loaded = load_font(path)
expect(loaded).to_not_be_nil()
val handle = loaded as std.nogc_sync_mut.io.font_ffi.FontHandle
val parsed = parse_offset_table(rt_file_read_bytes(path))
expect(parsed).to_not_equal(None)
val font = sk_font_new(sk_typeface_from_attached_font("Noto Emoji", sk_font_style_normal(), path, handle.handle), 12.0)
val bound = shaper_with_ot_face(shaper_new(fallback_chain_new(font)), handle.handle, parsed.unwrap())
val single = shaper_shape_with_language(bound, [128512u32], font, 0.0, 0.0, "und")[0]
expect single.font_handle to_equal handle.handle
expect single.font_generation to_equal handle.generation
expect single.glyph_indices_valid to_equal true
expect single.substitution_complete to_equal true
expect single.positioning_complete to_equal true
val single_material = shaped_run_to_font_glyph_run(single)
expect single_material.valid to_equal true
val sequence = shaper_shape_with_language(bound, [128512u32, 128512u32], font, 0.0, 0.0, "und")[0]
expect sequence.glyph_indices_valid to_equal false
val sequence_material = shaped_run_to_font_glyph_run(sequence)
expect sequence_material.valid to_equal false
val other = shaper_shape_with_language(bound, [128513u32], font, 0.0, 0.0, "und")[0]
expect other.substitution_complete to_equal false
expect shaped_run_to_font_glyph_run(other).valid to_equal false
val impostor_font = sk_font_new(sk_typeface_from_attached_font("Not Noto Emoji", sk_font_style_normal(), "not-pinned.ttf", handle.handle), 12.0)
val impostor = shaper_with_ot_face(shaper_new(fallback_chain_new(impostor_font)), handle.handle, parsed.unwrap())
val wrong_face = shaper_shape_with_language(impostor, [128512u32], impostor_font, 0.0, 0.0, "und")[0]
expect wrong_face.glyph_indices_valid to_equal true
expect wrong_face.substitution_complete to_equal false
expect shaped_run_to_font_glyph_run(wrong_face).valid to_equal false
free_font(handle)
```

</details>

#### uses OpenType data bound to the face selected by fallback

- uses OpenType data bound to the face selected by fallback
   - Expected: cross_bound.ot_faces.len() equals `0`
   - Expected: run.font_handle equals `emoji_handle.handle`
   - Expected: run.glyph_indices_valid is true
   - Expected: run.substitution_complete is true
   - Expected: run.positioning_complete is true
   - Expected: emoji_material.valid is true
   - Expected: emoji_material.face_id equals `emoji_handle.handle`
   - Expected: legacy.glyph_ids[0] equals `99u32`
   - Expected: stale.glyph_indices_valid is false
   - Expected: stale.glyph_ids[0] equals `128512u32`


<details>
<summary>Executable SSpec</summary>

Runnable source: 40 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("uses OpenType data bound to the face selected by fallback")
val primary_path = "src/compiler_rust/vendor/ttf-parser/tests/fonts/demo.ttf"
val emoji_path = "assets/fonts/google-fonts/ofl/notoemoji/NotoEmoji[wght].ttf"
val primary_loaded = load_font(primary_path)
val emoji_loaded = load_font(emoji_path)
expect(primary_loaded).to_not_be_nil()
expect(emoji_loaded).to_not_be_nil()
val primary_handle = primary_loaded as std.nogc_sync_mut.io.font_ffi.FontHandle
val emoji_handle = emoji_loaded as std.nogc_sync_mut.io.font_ffi.FontHandle
val primary_parsed = parse_offset_table(rt_file_read_bytes(primary_path))
val emoji_parsed = parse_offset_table(rt_file_read_bytes(emoji_path))
expect(primary_parsed).to_not_equal(None)
expect(emoji_parsed).to_not_equal(None)
val primary = sk_font_new(sk_typeface_from_attached_font("Demo Latin", sk_font_style_normal(), primary_path, primary_handle.handle), 12.0)
val emoji = sk_font_new(sk_typeface_from_attached_font("Noto Emoji", sk_font_style_normal(), emoji_path, emoji_handle.handle), 12.0)
val chain = fallback_chain_add(fallback_chain_new(primary), emoji)
var bound = shaper_with_ot_face(shaper_new(chain), primary_handle.handle, primary_parsed.unwrap())
bound = shaper_with_ot_face(bound, emoji_handle.handle, emoji_parsed.unwrap())
val cross_bound = shaper_with_ot_face(shaper_new(chain), primary_handle.handle, emoji_parsed.unwrap())
expect(cross_bound.ot_faces.len()).to_equal(0)
val run = shaper_shape_with_language(bound, [128512u32], primary, 0.0, 0.0, "und")[0]
expect(run.font_handle).to_equal(emoji_handle.handle)
expect(run.glyph_ids[0]).to_not_equal(128512u32)
expect(run.glyph_indices_valid).to_equal(true)
expect(run.substitution_complete).to_equal(true)
expect(run.positioning_complete).to_equal(true)
val emoji_material = shaped_run_to_font_glyph_run(run)
expect(emoji_material.valid).to_equal(true)
expect(emoji_material.face_id).to_equal(emoji_handle.handle)
val handleless_chain = fallback_chain_add(fallback_chain_new(sk_font_default()), emoji)
var mixed = shaper_with_ot_font(shaper_new(handleless_chain), primary_parsed.unwrap())
mixed = shaper_with_ot_face(mixed, emoji_handle.handle, emoji_parsed.unwrap())
val legacy = shaper_shape_with_language(mixed, [65u32], sk_font_default(), 0.0, 0.0, "en")[0]
expect(legacy.glyph_ids[0]).to_equal(99u32)
free_font(emoji_handle)
val stale = shaper_shape_with_language(bound, [128512u32], primary, 0.0, 0.0, "und")[0]
expect(stale.glyph_indices_valid).to_equal(false)
expect(stale.glyph_ids[0]).to_equal(128512u32)
free_font(primary_handle)
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
# @req REQ-SSPEC-LIB
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
# @req REQ-SSPEC-LIB
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
# @req REQ-SSPEC-LIB
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
# @req REQ-SSPEC-LIB
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
# @req REQ-SSPEC-LIB
step("Latin run has correct script")
val chain = system_default_chain()
val shaper = shaper_new(chain)
val cps = ascii_to_codepoints("hi")
val runs = shaper_shape(shaper, cps, sk_font_default(), 0.0, 0.0)
val run = runs[0]
expect run.script to_equal Script.Latin
```

</details>

#### unbound Latin diagnostic keeps codepoint identity and stays invalid

- unbound Latin diagnostic keeps codepoint identity and stays invalid


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("unbound Latin diagnostic keeps codepoint identity and stays invalid")
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
expect run.glyph_indices_valid to_equal false
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
# @req REQ-SSPEC-LIB
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
# @req REQ-SSPEC-LIB
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
# @req REQ-SSPEC-LIB
step("second run of mixed text is Arabic")
val chain = system_default_chain()
val shaper = shaper_new(chain)
val cps: [u32] = [65 as u32, 1576 as u32]
val runs = shaper_shape(shaper, cps, sk_font_default(), 0.0, 0.0)
val second_run = runs[1]
expect second_run.script to_equal Script.Arabic
```

</details>

#### places the second script run after the first run instead of overlapping

- places the second script run after the first run instead of overlapping


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("places the second script run after the first run instead of overlapping")
val shaper = shaper_new(system_default_chain())
val runs = shaper_shape(shaper, [65u32, 1576u32], sk_font_default(), 10.0, 0.0)
expect runs[1].positions[0].x to_equal runs[0].positions[0].x + runs[0].glyphs[0].x_advance
expect runs[1].positions[0].y to_equal runs[0].positions[0].y
```

</details>

### shaper_shape: provisional Arabic joining classification

#### Arabic run is RTL

- Arabic run is RTL


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
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

#### keeps absolute logical clusters through visual reversal and fails closed

- keeps absolute logical clusters through visual reversal and fails closed


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("keeps absolute logical clusters through visual reversal and fails closed")
val shaper = shaper_new(system_default_chain())
val run = shaper_shape_with_language(shaper, [1575u32, 1576u32, 1580u32], sk_font_default(), 0.0, 0.0, "ar")[0]
expect run.language to_equal "ar"
expect run.glyphs[0].cluster to_equal 2
expect run.glyphs[1].cluster to_equal 1
expect run.glyphs[2].cluster to_equal 0
expect run.glyph_indices_valid to_equal false
expect run.substitution_complete to_equal false
expect run.positioning_complete to_equal false
```

</details>

#### Arabic sequence produces exactly 1 run

- Arabic sequence produces exactly 1 run


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
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
# @req REQ-SSPEC-LIB
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
# @req REQ-SSPEC-LIB
step("isolated Arabic letter gets Isolated join form")
val cps: [u32] = [1575 as u32]
val form = arabic_join_form(cps, 0)
expect form to_equal ArabicJoinForm.Isolated
```

</details>

### shaper_shape: provisional Devanagari reph classification

#### Devanagari ra (2352) is classified as Reph

- Devanagari ra (2352) is classified as Reph


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
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
# @req REQ-SSPEC-LIB
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
# @req REQ-SSPEC-LIB
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
# @req REQ-SSPEC-LIB
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
# @req REQ-SSPEC-LIB
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

Runnable source: 20 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
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
expect run.glyphs[0].cluster to_equal 2
expect run.glyphs[1].cluster to_equal 0
expect run.glyphs[2].cluster to_equal 1
expect run.glyph_indices_valid to_equal false
```

</details>

### shaper metadata

#### propagates language, defaults empty language, and exposes current placement honestly

- propagates language, defaults empty language, and exposes current placement honestly


<details>
<summary>Executable SSpec</summary>

Runnable source: 29 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("propagates language, defaults empty language, and exposes current placement honestly")
val shaper = shaper_new(system_default_chain())
val latin_runs = shaper_shape_with_language(shaper, [69u32, 241u32, 111u32], sk_font_default(), 0.0, 0.0, "es")
expect latin_runs.len() to_equal 1
val latin = latin_runs[0]
expect latin.script to_equal Script.Latin
expect latin.language to_equal "es"
expect latin.glyphs.len() to_equal 3
expect latin.glyphs[0].cluster to_equal 0
expect latin.glyphs[1].cluster to_equal 1
expect latin.glyphs[2].cluster to_equal 2
expect latin.glyphs[1].x_offset to_equal 0.0
expect latin.glyphs[1].y_offset to_equal 0.0
expect latin.glyphs[1].y_advance to_equal 0.0
expect latin.positioning_complete to_equal false
val defaulted = shaper_shape_with_language(shaper, [65u32], sk_font_default(), 0.0, 0.0, "")[0]
expect defaulted.language to_equal "und"
val legacy = shaper_shape(shaper, [65u32], sk_font_default(), 0.0, 0.0)
val explicit = shaper_shape_with_language(shaper, [65u32], sk_font_default(), 0.0, 0.0, "und")
expect legacy.len() to_equal explicit.len()
expect legacy[0].script to_equal explicit[0].script
expect legacy[0].glyph_ids to_equal explicit[0].glyph_ids
expect legacy[0].positions[0].x to_equal explicit[0].positions[0].x
expect legacy[0].glyphs[0].source_index to_equal explicit[0].glyphs[0].source_index
expect legacy[0].glyph_indices_valid to_equal explicit[0].glyph_indices_valid
expect legacy[0].substitution_complete to_equal explicit[0].substitution_complete
expect legacy[0].positioning_complete to_equal explicit[0].positioning_complete
expect legacy[0].language to_equal "und"
```

</details>

#### shares a Thai cluster between a base and following mark

- shares a Thai cluster between a base and following mark


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("shares a Thai cluster between a base and following mark")
val shaper = shaper_new(system_default_chain())
val run = shaper_shape_with_language(shaper, [3585u32, 3656u32], sk_font_default(), 0.0, 0.0, "th")[0]
expect run.glyphs[0].source_index to_equal 0
expect run.glyphs[1].source_index to_equal 1
expect run.glyphs[0].cluster to_equal 0
expect run.glyphs[1].cluster to_equal 0
expect run.glyph_indices_valid to_equal false
```

</details>

### shaper_shape: unbound ASCII identity diagnostic

#### 3 ASCII codepoints produce 3 glyph ids

- 3 ASCII codepoints produce 3 glyph ids


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
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
# @req REQ-SSPEC-LIB
step("positions count matches glyph count")
val chain = system_default_chain()
val shaper = shaper_new(chain)
val cps: [u32] = [72 as u32, 105 as u32, 33 as u32]
val runs = shaper_shape(shaper, cps, sk_font_default(), 0.0, 0.0)
val run = runs[0]
expect run.positions.len() to_equal run.glyph_ids.len()
```

</details>

### shaper_shape: fallback placement estimate without OtFont

#### positions are monotonically increasing for LTR Latin

- positions are monotonically increasing for LTR Latin


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
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
# @req REQ-SSPEC-LIB
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
# @req REQ-SSPEC-LIB
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
# @req REQ-SSPEC-LIB
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
# @req REQ-SSPEC-LIB
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
# @req REQ-SSPEC-LIB
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
# @req REQ-SSPEC-LIB
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
# @req REQ-SSPEC-LIB
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
# @req REQ-SSPEC-LIB
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
# @req REQ-SSPEC-LIB
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
# @req REQ-SSPEC-LIB
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
# @req REQ-SSPEC-LIB
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
# @req REQ-SSPEC-LIB
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
# @req REQ-SSPEC-LIB
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
# @req REQ-SSPEC-LIB
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
# @req REQ-SSPEC-LIB
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
# @req REQ-SSPEC-LIB
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
# @req REQ-SSPEC-LIB
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
| Source | `test/01_unit/lib/skia/shaper_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering script_of: Latin range, Common and Inherited script resolution, script_of: Bengali range, script_of: Hebrew range, script_of: Arabic range, script_of: Cyrillic range, script_of: CJK range, selected font corpus shaping metadata, script_is_rtl, feature_tag, FallbackChain, Shaper, ascii_to_codepoints, shaper_shape: empty text, shaper_shape: ASCII Latin text, shaper_shape: mixed Latin + Arabic, shaper_shape: provisional Arabic joining classification, shaper_shape: provisional Devanagari reph classification, shaper metadata, shaper_shape: unbound ASCII identity diagnostic, shaper_shape: fallback placement estimate without OtFont, classify_thai_char, classify_myanmar_char, classify_khmer_char, classify_tibetan_char, classify_hangul_char, classify_hebrew_char, classify_mongolian_char.
- script_of: Latin range
- Common and Inherited script resolution
- script_of: Bengali range
- script_of: Hebrew range
- script_of: Arabic range
- script_of: Cyrillic range
- script_of: CJK range
- selected font corpus shaping metadata
- script_is_rtl
- feature_tag
- FallbackChain
- Shaper
- ascii_to_codepoints
- shaper_shape: empty text
- shaper_shape: ASCII Latin text
- shaper_shape: mixed Latin + Arabic
- shaper_shape: provisional Arabic joining classification
- shaper_shape: provisional Devanagari reph classification
- shaper metadata
- shaper_shape: unbound ASCII identity diagnostic
- shaper_shape: fallback placement estimate without OtFont
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
| Total scenarios | 83 |
| Active scenarios | 83 |
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

- Canonical SPipe generation for source `94552c8fe6c8e651f0be7e498c97404314042e671e8792c4a1ead803ba455f05`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `94552c8fe6c8e651f0be7e498c97404314042e671e8792c4a1ead803ba455f05`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `94552c8fe6c8e651f0be7e498c97404314042e671e8792c4a1ead803ba455f05`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **88/100**; effective score: **88/100**; blockers: **0**.

SSpec documentization score: 88/100
source: test/01_unit/lib/skia/shaper_spec.spl
mirror: doc/06_spec/01_unit/lib/skia/shaper_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=80
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/lib/skia/shaper_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/lib/skia/shaper_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/lib/skia/shaper_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-20): 2 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/lib/skia/shaper_spec.spl:67:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'ASCII 'A' (0x0041) is Latin' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/skia/shaper_spec.spl:74:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'ASCII non-letters are Common' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/skia/shaper_spec.spl:83:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'selected Latin-1 witnesses stay in one script' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
