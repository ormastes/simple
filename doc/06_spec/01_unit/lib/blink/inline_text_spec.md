# Inline Text Measurement Specification

> Purpose: Prove that codepoint column classification.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 41 | 41 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Inline Text Measurement Specification

Purpose: Prove that codepoint column classification.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Browser / Blink |
| Status | Active |
| Source | `test/01_unit/lib/blink/inline_text_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Purpose and audience
Purpose: Prove that codepoint column classification.
Audience: compiler and tooling engineers who maintain this spec.

## Scenarios

### codepoint column classification

#### an ASCII letter occupies one column

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- classify the codepoint for 'A'
   - Expected: codepoint_cells(65) equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-LIB-BLINK-001
step("classify the codepoint for 'A'")
expect(codepoint_cells(65)).to_equal(1)  # oracle: 1 — named expected value from the requirement
```

</details>

#### a CJK ideograph occupies two columns

- a CJK ideograph occupies two columns
- classify U+6F22 (漢), an East-Asian wide glyph
   - Expected: is_wide_codepoint(0x6F22) is true
- confirm it is charged two columns, not one
   - Expected: codepoint_cells(0x6F22) equals `2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("a CJK ideograph occupies two columns")
step("classify U+6F22 (漢), an East-Asian wide glyph")
expect(is_wide_codepoint(0x6F22)).to_equal(true)
step("confirm it is charged two columns, not one")
expect(codepoint_cells(0x6F22)).to_equal(2)  # oracle: 2 — named expected value from the requirement
```

</details>

#### an emoji occupies two columns

- an emoji occupies two columns
- classify U+1F600, in the emoji plane
   - Expected: codepoint_cells(0x1F600) equals `2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("an emoji occupies two columns")
step("classify U+1F600, in the emoji plane")
expect(codepoint_cells(0x1F600)).to_equal(2)  # oracle: 2 — named expected value from the requirement
```

</details>

#### a combining accent occupies no column of its own

- a combining accent occupies no column of its own
- classify U+0301 COMBINING ACUTE ACCENT
   - Expected: is_zero_width_codepoint(0x0301) is true
- confirm it adds nothing to the advance
   - Expected: codepoint_cells(0x0301) equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("a combining accent occupies no column of its own")
step("classify U+0301 COMBINING ACUTE ACCENT")
expect(is_zero_width_codepoint(0x0301)).to_equal(true)
step("confirm it adds nothing to the advance")
expect(codepoint_cells(0x0301)).to_equal(0)  # oracle: 0 — named expected value from the requirement
```

</details>

#### a zero-width joiner occupies no column

- a zero-width joiner occupies no column
- Verify: a zero-width joiner occupies no column
   - Expected: codepoint_cells(0x200D) equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("a zero-width joiner occupies no column")
step("Verify: a zero-width joiner occupies no column")
expect(codepoint_cells(0x200D)).to_equal(0)  # oracle: 0 — named expected value from the requirement
```

</details>

### text_cell_width counts characters, not bytes

#### pure ASCII measures one column per letter

- pure ASCII measures one column per letter
- measure "abc"
   - Expected: text_cell_width("abc") equals `3`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("pure ASCII measures one column per letter")
step("measure \"abc\"")
expect(text_cell_width("abc")).to_equal(3)
```

</details>

#### a two-byte accented character still measures one column

- a two-byte accented character still measures one column
- measure "aé", which is three BYTES but two characters
   - Expected: text_cell_width("aé") equals `2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("a two-byte accented character still measures one column")
step("measure \"aé\", which is three BYTES but two characters")
# @req A multi-byte UTF-8 character must be charged once, not once per byte.
expect(text_cell_width("aé")).to_equal(2)
```

</details>

#### a three-byte CJK glyph measures two columns, not three

- a three-byte CJK glyph measures two columns, not three
- measure "漢", which is three BYTES and one double-width glyph
   - Expected: text_cell_width("漢") equals `2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("a three-byte CJK glyph measures two columns, not three")
step("measure \"漢\", which is three BYTES and one double-width glyph")
# @req A wide glyph is charged by its drawn width, never by its byte length.
expect(text_cell_width("漢")).to_equal(2)
```

</details>

#### a mixed ASCII, accented and CJK run measures by drawn width

- a mixed ASCII, accented and CJK run measures by drawn width
- measure "aé漢" — 6 bytes, 3 characters, 4 drawn columns
   - Expected: text_cell_width("aé漢") equals `4`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("a mixed ASCII, accented and CJK run measures by drawn width")
step("measure \"aé漢\" — 6 bytes, 3 characters, 4 drawn columns")
expect(text_cell_width("aé漢")).to_equal(4)
```

</details>

#### a combining accent adds no column to the letter it attaches to

- a combining accent adds no column to the letter it attaches to
- measure "e" followed by U+0301
   - Expected: text_cell_width("e\u{0301}") equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("a combining accent adds no column to the letter it attaches to")
step("measure \"e\" followed by U+0301")
expect(text_cell_width("e\u{0301}")).to_equal(1)
```

</details>

#### the empty string measures zero

- the empty string measures zero
- Verify: the empty string measures zero
   - Expected: text_cell_width("") equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("the empty string measures zero")
step("Verify: the empty string measures zero")
expect(text_cell_width("")).to_equal(0)
```

</details>

### monospace_metrics

#### a 16px font advances 10px per character

- a 16px font advances 10px per character
- resolve metrics for a 16px font with no extra spacing
- 16px is scale 2, so the advance is 5 * 2
   - Expected: glyph_scale(16) equals `2`
   - Expected: m.cell_advance_px equals `10`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("a 16px font advances 10px per character")
step("resolve metrics for a 16px font with no extra spacing")
val m = monospace_metrics(16, 0, 0, 0)
step("16px is scale 2, so the advance is 5 * 2")
expect(glyph_scale(16)).to_equal(2)  # oracle: 2 — named expected value from the requirement
expect(m.cell_advance_px).to_equal(10)  # oracle: 10 — named expected value from the requirement
```

</details>

#### a tiny font falls back to the minimum 4px advance

- a tiny font falls back to the minimum 4px advance
- Verify: a tiny font falls back to the minimum 4px advance
   - Expected: m.cell_advance_px equals `4`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("a tiny font falls back to the minimum 4px advance")
step("Verify: a tiny font falls back to the minimum 4px advance")
val m = monospace_metrics(8, 0, 0, 0)
expect(m.cell_advance_px).to_equal(4)  # oracle: 4 — named expected value from the requirement
```

</details>

#### letter-spacing widens every character

- letter-spacing widens every character
- resolve a 16px font with 3px letter-spacing
   - Expected: m.cell_advance_px equals `13`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("letter-spacing widens every character")
step("resolve a 16px font with 3px letter-spacing")
val m = monospace_metrics(16, 3, 0, 0)
expect(m.cell_advance_px).to_equal(13)  # oracle: 13 — named expected value from the requirement
```

</details>

#### a negative letter-spacing can never collapse the advance to zero

- a negative letter-spacing can never collapse the advance to zero
- ask for a letter-spacing far more negative than the glyph is wide
   - Expected: m.cell_advance_px equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("a negative letter-spacing can never collapse the advance to zero")
step("ask for a letter-spacing far more negative than the glyph is wide")
# @req A text run must always measure at least one pixel per character
#      so a line box can never collapse to nothing.
val m = monospace_metrics(16, -99, 0, 0)
expect(m.cell_advance_px).to_equal(1)  # oracle: 1 — named expected value from the requirement
```

</details>

#### an explicit line-height overrides the font's natural one

- an explicit line-height overrides the font's natural one
- Verify: an explicit line-height overrides the font's natural one
   - Expected: natural.line_height_px equals `18`
   - Expected: forced.line_height_px equals `40`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("an explicit line-height overrides the font's natural one")
step("Verify: an explicit line-height overrides the font's natural one")
val natural = monospace_metrics(16, 0, 0, 0)
expect(natural.line_height_px).to_equal(18)  # oracle: 18 — named expected value from the requirement
val forced = monospace_metrics(16, 0, 0, 40)
expect(forced.line_height_px).to_equal(40)  # oracle: 40 — named expected value from the requirement
```

</details>

### measure_text advance width

#### three ASCII letters at 16px measure 30px

- three ASCII letters at 16px measure 30px
- Verify: three ASCII letters at 16px measure 30px
   - Expected: measure_text("abc", m) equals `30`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("three ASCII letters at 16px measure 30px")
step("Verify: three ASCII letters at 16px measure 30px")
val m = monospace_metrics(16, 0, 0, 0)
expect(measure_text("abc", m)).to_equal(30)
```

</details>

#### a space is narrower than a letter

- a space is narrower than a letter
- measure a single space against a single letter at 16px
   - Expected: measure_text(" ", m) equals `5`
   - Expected: measure_text("a", m) equals `10`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("a space is narrower than a letter")
step("measure a single space against a single letter at 16px")
val m = monospace_metrics(16, 0, 0, 0)
expect(measure_text(" ", m)).to_equal(5)
expect(measure_text("a", m)).to_equal(10)
```

</details>

#### an accented character measures the same as a plain one

- an accented character measures the same as a plain one
- compare "é" against "e" — same drawn width, different byte length
   - Expected: measure_text("é", m) equals `measure_text("e", m)`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("an accented character measures the same as a plain one")
step("compare \"é\" against \"e\" — same drawn width, different byte length")
# @req Measurement must not vary with a character's UTF-8 encoding length.
val m = monospace_metrics(16, 0, 0, 0)
expect(measure_text("é", m)).to_equal(measure_text("e", m))
```

</details>

#### a CJK glyph measures exactly twice a Latin letter

- a CJK glyph measures exactly twice a Latin letter
- compare "漢" against "a" at 16px
   - Expected: measure_text("漢", m) equals `2 * measure_text("a", m)`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("a CJK glyph measures exactly twice a Latin letter")
step("compare \"漢\" against \"a\" at 16px")
val m = monospace_metrics(16, 0, 0, 0)
expect(measure_text("漢", m)).to_equal(2 * measure_text("a", m))
```

</details>

#### a combining accent adds nothing to the run's width

- a combining accent adds nothing to the run's width
- Verify: a combining accent adds nothing to the run's width
   - Expected: measure_text("e\u{0301}", m) equals `measure_text("e", m)`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("a combining accent adds nothing to the run's width")
step("Verify: a combining accent adds nothing to the run's width")
val m = monospace_metrics(16, 0, 0, 0)
expect(measure_text("e\u{0301}", m)).to_equal(measure_text("e", m))
```

</details>

#### the empty string measures zero pixels

- the empty string measures zero pixels
- Verify: the empty string measures zero pixels
   - Expected: measure_text("", m) equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("the empty string measures zero pixels")
step("Verify: the empty string measures zero pixels")
val m = monospace_metrics(16, 0, 0, 0)
expect(measure_text("", m)).to_equal(0)
```

</details>

### measure_range

#### measures only the requested character span

- measures only the requested character span
- measure characters 1 through 3 of "abcd" at 16px
   - Expected: measure_range(cps, 1, 3, m) equals `20`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("measures only the requested character span")
step("measure characters 1 through 3 of \"abcd\" at 16px")
val m = monospace_metrics(16, 0, 0, 0)
val cps = text_codepoints("abcd")
expect(measure_range(cps, 1, 3, m)).to_equal(20)  # oracle: 20 — named expected value from the requirement
```

</details>

#### a span reaching past the end measures the clamped overlap

- a span reaching past the end measures the clamped overlap
- ask for characters 2..99 of a 4-character run
   - Expected: measure_range(cps, 2, 99, m) equals `20`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("a span reaching past the end measures the clamped overlap")
step("ask for characters 2..99 of a 4-character run")
# @req An out-of-range span must not read past the text.
val m = monospace_metrics(16, 0, 0, 0)
val cps = text_codepoints("abcd")
expect(measure_range(cps, 2, 99, m)).to_equal(20)  # oracle: 20 — named expected value from the requirement
```

</details>

#### an inverted span measures zero

- an inverted span measures zero
- Verify: an inverted span measures zero
   - Expected: measure_range(cps, 3, 1, m) equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("an inverted span measures zero")
step("Verify: an inverted span measures zero")
val m = monospace_metrics(16, 0, 0, 0)
val cps = text_codepoints("abcd")
expect(measure_range(cps, 3, 1, m)).to_equal(0)  # oracle: 0 — named expected value from the requirement
```

</details>

### baseline_offset_px

#### the baseline sits inside the line box, below its top

- the baseline sits inside the line box, below its top
- Verify: the baseline sits inside the line box, below its top
   - Expected: b > 0 is true
   - Expected: b < m.line_height_px is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("the baseline sits inside the line box, below its top")
step("Verify: the baseline sits inside the line box, below its top")
val m = monospace_metrics(16, 0, 0, 0)
val b = baseline_offset_px(m)
expect(b > 0).to_equal(true)
expect(b < m.line_height_px).to_equal(true)
```

</details>

#### a one-pixel line box still has a baseline on its first row

- a one-pixel line box still has a baseline on its first row
- Verify: a one-pixel line box still has a baseline on its first row
   - Expected: baseline_offset_px(m) equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("a one-pixel line box still has a baseline on its first row")
step("Verify: a one-pixel line box still has a baseline on its first row")
# @req The baseline must never be above the line box.
val m = monospace_metrics(16, 0, 0, 1)
expect(baseline_offset_px(m)).to_equal(1)  # oracle: 1 — named expected value from the requirement
```

</details>

### wrap_line_end

#### text that fits entirely reports the end of the text

- text that fits entirely reports the end of the text
- Verify: text that fits entirely reports the end of the text
   - Expected: wrap_line_end(cps, 0, 1000, m) equals `3`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("text that fits entirely reports the end of the text")
step("Verify: text that fits entirely reports the end of the text")
val m = monospace_metrics(16, 0, 0, 0)
val cps = text_codepoints("abc")
expect(wrap_line_end(cps, 0, 1000, m)).to_equal(3)  # oracle: 3 — named expected value from the requirement
```

</details>

#### a break falls on the last space before the overflow

- a break falls on the last space before the overflow
- wrap "aa bb cc" at 16px into a 60px box
   - Expected: wrap_line_end(cps, 0, 60, m) equals `5`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("a break falls on the last space before the overflow")
step("wrap \"aa bb cc\" at 16px into a 60px box")
val m = monospace_metrics(16, 0, 0, 0)
val cps = text_codepoints("aa bb cc")
expect(wrap_line_end(cps, 0, 60, m)).to_equal(5)  # oracle: 5 — named expected value from the requirement
```

</details>

#### a single word wider than the box is broken mid-word

- a single word wider than the box is broken mid-word
- wrap the unbreakable "aaaaaa" into a 25px box
   - Expected: e > 0 is true
   - Expected: e < 6 is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("a single word wider than the box is broken mid-word")
step("wrap the unbreakable \"aaaaaa\" into a 25px box")
# @req A word too long for the line must still make progress, or
#      wrapping would loop forever.
val m = monospace_metrics(16, 0, 0, 0)
val cps = text_codepoints("aaaaaa")
val e = wrap_line_end(cps, 0, 25, m)
expect(e > 0).to_equal(true)
expect(e < 6).to_equal(true)
```

</details>

#### a zero-width box still consumes one character per line

- a zero-width box still consumes one character per line
- Verify: a zero-width box still consumes one character per line
   - Expected: wrap_line_end(cps, 0, 0, m) equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("a zero-width box still consumes one character per line")
step("Verify: a zero-width box still consumes one character per line")
val m = monospace_metrics(16, 0, 0, 0)
val cps = text_codepoints("abc")
expect(wrap_line_end(cps, 0, 0, m)).to_equal(1)  # oracle: 1 — named expected value from the requirement
```

</details>

### wrap_text_lines

#### text that fits stays on one line

- text that fits stays on one line
- Verify: text that fits stays on one line
   - Expected: lines.len() equals `1`
   - Expected: lines[0] equals `hello`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("text that fits stays on one line")
step("Verify: text that fits stays on one line")
val m = monospace_metrics(16, 0, 0, 0)
val lines = wrap_text_lines("hello", 1000, m)
expect(lines.len()).to_equal(1)  # oracle: 1 — named expected value from the requirement
expect(lines[0]).to_equal("hello")
```

</details>

#### a long sentence breaks into whole words

- a long sentence breaks into whole words
- wrap "aa bb cc" at 16px into a 60px box
   - Expected: lines.len() equals `2`
   - Expected: lines[0] equals `aa bb`
   - Expected: lines[1] equals `cc`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("a long sentence breaks into whole words")
step("wrap \"aa bb cc\" at 16px into a 60px box")
val m = monospace_metrics(16, 0, 0, 0)
val lines = wrap_text_lines("aa bb cc", 60, m)
expect(lines.len()).to_equal(2)  # oracle: 2 — named expected value from the requirement
expect(lines[0]).to_equal("aa bb")
expect(lines[1]).to_equal("cc")
```

</details>

#### wrapping a CJK run keeps every glyph intact

- wrapping a CJK run keeps every glyph intact
- wrap four CJK glyphs into a box two glyphs wide
   - Expected: lines.len() equals `2`
   - Expected: lines[0] equals `漢字`
   - Expected: lines[1] equals `漢字`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("wrapping a CJK run keeps every glyph intact")
step("wrap four CJK glyphs into a box two glyphs wide")
# @req Wrapping must split between characters, never inside a
#      multi-byte character.
val m = monospace_metrics(16, 0, 0, 0)
val lines = wrap_text_lines("漢字漢字", 40, m)
expect(lines.len()).to_equal(2)  # oracle: 2 — named expected value from the requirement
expect(lines[0]).to_equal("漢字")
expect(lines[1]).to_equal("漢字")
```

</details>

#### an empty paragraph still occupies one line

- an empty paragraph still occupies one line
- Verify: an empty paragraph still occupies one line
   - Expected: lines.len() equals `1`
   - Expected: lines[0] equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("an empty paragraph still occupies one line")
step("Verify: an empty paragraph still occupies one line")
val m = monospace_metrics(16, 0, 0, 0)
val lines = wrap_text_lines("", 100, m)
expect(lines.len()).to_equal(1)  # oracle: 1 — named expected value from the requirement
expect(lines[0]).to_equal("")
```

</details>

### blink inline text API

#### a run's advance width matches the shared measurement

- a run's advance width matches the shared measurement
- measure "abc" through the blink face at 16px
   - Expected: inline_text_advance_width("abc", f) equals `30`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("a run's advance width matches the shared measurement")
step("measure \"abc\" through the blink face at 16px")
val f = inline_font(16)
expect(inline_text_advance_width("abc", f)).to_equal(30)
```

</details>

#### blink charges a CJK glyph double, as the shared layer does

- blink charges a CJK glyph double, as the shared layer does
- Verify: blink charges a CJK glyph double, as the shared layer does
   - Expected: inline_text_advance_width("漢", f) equals `20`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("blink charges a CJK glyph double, as the shared layer does")
step("Verify: blink charges a CJK glyph double, as the shared layer does")
val f = inline_font(16)
expect(inline_text_advance_width("漢", f)).to_equal(20)
```

</details>

#### blink reports a cell width independent of font size

- blink reports a cell width independent of font size
- Verify: blink reports a cell width independent of font size
   - Expected: inline_text_cell_width("aé漢") equals `4`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("blink reports a cell width independent of font size")
step("Verify: blink reports a cell width independent of font size")
expect(inline_text_cell_width("aé漢")).to_equal(4)
```

</details>

#### a line box at 16px is 18px tall with a baseline inside it

- a line box at 16px is 18px tall with a baseline inside it
- Verify: a line box at 16px is 18px tall with a baseline inside it
   - Expected: inline_text_line_height(f) equals `18`
   - Expected: inline_text_baseline(f) < 18 is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("a line box at 16px is 18px tall with a baseline inside it")
step("Verify: a line box at 16px is 18px tall with a baseline inside it")
val f = inline_font(16)
expect(inline_text_line_height(f)).to_equal(18)  # oracle: 18 — named expected value from the requirement
expect(inline_text_baseline(f) < 18).to_equal(true)
```

</details>

#### laying out a paragraph reports its lines and used box

- laying out a paragraph reports its lines and used box
- lay out "aa bb cc" into a 60px-wide box at 16px
   - Expected: block.lines.len() equals `2`
- the used width is the widest line, not the box width
   - Expected: block.width_px equals `45`
- the used height is one line box per line
   - Expected: block.height_px equals `36`


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("laying out a paragraph reports its lines and used box")
step("lay out \"aa bb cc\" into a 60px-wide box at 16px")
val f = inline_font(16)
val block = layout_inline_text("aa bb cc", 60, f)
expect(block.lines.len()).to_equal(2)  # oracle: 2 — named expected value from the requirement
step("the used width is the widest line, not the box width")
# "aa bb" is 4 letters at 10px plus one 5px space; the space the break
# consumed is not carried onto either line, so it is not charged.
expect(block.width_px).to_equal(45)  # oracle: 45 — named expected value from the requirement
step("the used height is one line box per line")
expect(block.height_px).to_equal(36)  # oracle: 36 — named expected value from the requirement
```

</details>

#### a paragraph never reports a width wider than its box

- a paragraph never reports a width wider than its box
- Verify: a paragraph never reports a width wider than its box
   - Expected: block.width_px <= 60 is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("a paragraph never reports a width wider than its box")
step("Verify: a paragraph never reports a width wider than its box")
val f = inline_font(16)
val block = layout_inline_text("aa bb cc dd ee", 60, f)
expect(block.width_px <= 60).to_equal(true)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 41 |
| Active scenarios | 41 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-LIB`
- `REQ-LIB-BLINK-001`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `9aa6ff84be560d45c7da7abcc4e386adcb0120966cb4e5237264450bfb58200b`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `9aa6ff84be560d45c7da7abcc4e386adcb0120966cb4e5237264450bfb58200b`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `9aa6ff84be560d45c7da7abcc4e386adcb0120966cb4e5237264450bfb58200b`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **86/100**; effective score: **86/100**; blockers: **0**.

SSpec documentization score: 86/100
source: test/01_unit/lib/blink/inline_text_spec.spl
mirror: doc/06_spec/01_unit/lib/blink/inline_text_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/lib/blink/inline_text_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/lib/blink/inline_text_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/lib/blink/inline_text_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 13 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/lib/blink/inline_text_spec.spl:75:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'an ASCII letter occupies one column' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/blink/inline_text_spec.spl:80:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'a CJK ideograph occupies two columns' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/blink/inline_text_spec.spl:88:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'an emoji occupies two columns' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
