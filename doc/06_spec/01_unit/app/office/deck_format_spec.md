# deck_format_spec

> Deck Format Parser — text format for Slides presentations.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 35 | 35 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# deck_format_spec

Deck Format Parser — text format for Slides presentations.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/01_unit/app/office/deck_format_spec.spl` |
| Updated | 2026-08-18 |
| Generator | `simple spipe-docgen` (Simple) |

Deck Format Parser — text format for Slides presentations.

Verifies parsing and serialization of deck text format:
- Slides separated by `---`
- First non-blank line is title
- Following non-blank lines are body boxes
- Blank lines skipped, empty slides skipped
- Round-trip preservation of content

## Scenarios

### Deck Format: Parsing
_Parser extracts slides, titles, and body lines from text format._

#### parses a single-slide deck

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val content = "Title\nBody text"
val slides = parse_deck(content)
expect(slides.len()).to_equal(1)
```

</details>

#### parses a two-slide deck separated by ---

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val content = "Slide 1 Title\nSlide 1 Body\n---\nSlide 2 Title\nSlide 2 Body"
val slides = parse_deck(content)
expect(slides.len()).to_equal(2)
```

</details>

#### assigns auto-generated slide ids

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val content = "Title1\n---\nTitle2"
val slides = parse_deck(content)
expect(slides[0].id).to_equal("slide1")
expect(slides[1].id).to_equal("slide2")
```

</details>

#### creates title element with correct id and dimensions

<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val content = "My Title\nBody"
val slides = parse_deck(content)
val slide = slides[0]
# Find title element
var title_found = false
for el in slide.elements:
    if el.id == "title":
        title_found = true
        expect(el.x).to_equal(60)
        expect(el.y).to_equal(60)
        expect(el.width).to_equal(840)
        expect(el.height).to_equal(120)
assert_true(title_found)
```

</details>

#### creates body elements with correct ids and positions

<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val content = "Title\nBody 1\nBody 2"
val slides = parse_deck(content)
val slide = slides[0]
# Count body elements
var body1_found = false
var body2_found = false
for el in slide.elements:
    if el.id == "body1":
        body1_found = true
        expect(el.y).to_equal(220)
    elif el.id == "body2":
        body2_found = true
        expect(el.y).to_equal(310)
assert_true(body1_found)
assert_true(body2_found)
```

</details>

#### skips blank lines within slides

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val content = "Title\n\n\nBody"
val slides = parse_deck(content)
expect(slides.len()).to_equal(1)
val slide = slides[0]
expect(slide.elements.len()).to_equal(2)
```

</details>

#### skips empty slides

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val content = "Title1\n---\n\n\n---\nTitle2"
val slides = parse_deck(content)
expect(slides.len()).to_equal(2)
expect(slides[0].id).to_equal("slide1")
expect(slides[1].id).to_equal("slide2")
```

</details>

### Deck Format: Serialization
_Serializer produces text format from slides._

#### serializes a single slide

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val content = "Title\nBody"
val slides = parse_deck(content)
val serialized = deck_to_text(slides)
expect(serialized).to_contain("Title")
expect(serialized).to_contain("Body")
```

</details>

#### joins multiple slides with --- separator

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val content = "Title1\nBody1\n---\nTitle2\nBody2"
val slides = parse_deck(content)
val serialized = deck_to_text(slides)
expect(serialized).to_contain("---")
```

</details>

#### preserves title text in round-trip

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val content = "My Important Title\nSome body text"
val slides = parse_deck(content)
val serialized = deck_to_text(slides)
expect(serialized).to_contain("My Important Title")
```

</details>

#### preserves body text in round-trip

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val content = "Title\nFirst body\nSecond body"
val slides = parse_deck(content)
val serialized = deck_to_text(slides)
expect(serialized).to_contain("First body")
expect(serialized).to_contain("Second body")
```

</details>

### Deck Format: Round-trip
_Parse and serialize preserves deck structure and content._

#### round-trip preserves single slide with title and body

<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val original = "Title\nBody"
val slides = parse_deck(original)
val serialized = deck_to_text(slides)
val reparsed = parse_deck(serialized)
expect(reparsed.len()).to_equal(1)
# Check title is preserved
var title_content = ""
for el in reparsed[0].elements:
    if el.id == "title":
        match el.kind:
            SlideElementKind.TextBox(content: c):
                title_content = c
            _:
                pass_do_nothing("non-textbox")
expect(title_content).to_equal("Title")
```

</details>

#### round-trip preserves multiple slides

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val original = "Slide1Title\nSlide1Body\n---\nSlide2Title\nSlide2Body"
val slides = parse_deck(original)
val serialized = deck_to_text(slides)
val reparsed = parse_deck(serialized)
expect(reparsed.len()).to_equal(2)
expect(reparsed[0].id).to_equal("slide1")
expect(reparsed[1].id).to_equal("slide2")
```

</details>

#### handles blank lines correctly in round-trip

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val original = "Title\n\nBody1\n\nBody2"
val slides = parse_deck(original)
expect(slides.len()).to_equal(1)
val serialized = deck_to_text(slides)
val reparsed = parse_deck(serialized)
expect(reparsed.len()).to_equal(1)
expect(reparsed[0].elements.len()).to_equal(3)
```

</details>

### Deck Format: speaker notes and transitions

#### parses an @notes: directive line into slide.notes

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val content = "Title\nBody\n@notes: remember the punchline"
val slides = parse_deck(content)
expect(slides.len()).to_equal(1)
expect(slides[0].notes).to_equal("remember the punchline")
```

</details>

#### parses an @transition: directive line into slide.transition

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val content = "Title\nBody\n@transition: fade"
val slides = parse_deck(content)
expect(slides[0].transition).to_equal("fade")
```

</details>

#### defaults notes and transition to empty when absent

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val content = "Title\nBody"
val slides = parse_deck(content)
expect(slides[0].notes).to_equal("")
expect(slides[0].transition).to_equal("")
```

</details>

#### excludes directive lines from title/body content

<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val content = "Title\nBody\n@notes: hidden\n@transition: wipe"
val slides = parse_deck(content)
val slide = slides[0]
var body_count = 0
for el in slide.elements:
    if el.id.starts_with("body"):
        body_count = body_count + 1
expect(body_count).to_equal(1)
```

</details>

#### serializes notes and transition back to @notes:/@transition: lines

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val content = "Title\nBody\n@notes: hi there\n@transition: push"
val slides = parse_deck(content)
val serialized = deck_to_text(slides)
expect(serialized).to_contain("@notes: hi there")
expect(serialized).to_contain("@transition: push")
```

</details>

#### round-trips notes and transition through parse/serialize/parse

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val original = "Title\nBody\n@notes: speaker note text\n@transition: wipe"
val slides = parse_deck(original)
val serialized = deck_to_text(slides)
val reparsed = parse_deck(serialized)
expect(reparsed.len()).to_equal(1)
expect(reparsed[0].notes).to_equal("speaker note text")
expect(reparsed[0].transition).to_equal("wipe")
```

</details>

#### round-trips a multi-slide deck with per-slide notes/transitions

<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val original = "Slide1\nBody1\n@notes: n1\n@transition: fade\n---\nSlide2\nBody2\n@notes: n2\n@transition: push"
val slides = parse_deck(original)
expect(slides.len()).to_equal(2)
expect(slides[0].notes).to_equal("n1")
expect(slides[0].transition).to_equal("fade")
expect(slides[1].notes).to_equal("n2")
expect(slides[1].transition).to_equal("push")
val reparsed = parse_deck(deck_to_text(slides))
expect(reparsed[0].notes).to_equal("n1")
expect(reparsed[1].transition).to_equal("push")
```

</details>

### Deck Format: nested bullets

#### parses a level-0 bullet line into a bullet element

<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val content = "Title\n- Point one"
val slides = parse_deck(content)
var bullet_content = ""
var bullet_found = false
for el in slides[0].elements:
    if el.id == "bullet0_1":
        bullet_found = true
        match el.kind:
            SlideElementKind.TextBox(content: c):
                bullet_content = c
            _:
                pass_do_nothing("non-textbox")
assert_true(bullet_found)
expect(bullet_content).to_equal("Point one")
```

</details>

#### parses 2-space and 4-space indents as levels 1 and 2

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val content = "Title\n- L0\n  - L1\n    - L2"
val slides = parse_deck(content)
var ids = ""
for el in slides[0].elements:
    if el.id.starts_with("bullet"):
        ids = "{ids}[{el.id}]"
expect(ids).to_equal("[bullet0_1][bullet1_2][bullet2_3]")
```

</details>

#### clamps deeper indentation to level 2

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val content = "Title\n      - Deep"
val slides = parse_deck(content)
var found = false
for el in slides[0].elements:
    if el.id == "bullet2_1":
        found = true
assert_true(found)
```

</details>

#### keeps plain body lines as body elements alongside bullets

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val content = "Title\n- Bullet\nPlain line"
val slides = parse_deck(content)
var ids = ""
for el in slides[0].elements:
    if el.id != "title":
        ids = "{ids}[{el.id}]"
expect(ids).to_equal("[bullet0_1][body2]")
```

</details>

#### treats a dash without a following space as plain body text

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val content = "Title\n-notabullet"
val slides = parse_deck(content)
var ids = ""
for el in slides[0].elements:
    if el.id != "title":
        ids = "{ids}[{el.id}]"
expect(ids).to_equal("[body1]")
```

</details>

#### serializes bullets back with indentation and marker

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val original = "Title\n- L0\n  - L1\n    - L2"
val slides = parse_deck(original)
val serialized = deck_to_text(slides)
expect(serialized).to_equal(original)
```

</details>

#### round-trips mixed bullets and plain lines exactly

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val original = "Agenda\n- Opening\n  - Welcome note\n- Closing\nPlain wrap-up"
val slides = parse_deck(original)
val serialized = deck_to_text(slides)
expect(serialized).to_equal(original)
```

</details>

### Deck Format: @layout directive

#### parses @layout: title-only into the TitleSlide layout

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val content = "Title\n@layout: title-only"
val slides = parse_deck(content)
expect(slide_layout_short_name(slides[0].layout)).to_equal("Title")
```

</details>

#### parses @layout: section into the SectionHeader layout

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val content = "Title\n@layout: section"
val slides = parse_deck(content)
expect(slide_layout_short_name(slides[0].layout)).to_equal("Section")
```

</details>

#### defaults to Blank for title-body, absent, and unknown tags

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val a = parse_deck("Title\n@layout: title-body")
val b = parse_deck("Title\nBody")
val c = parse_deck("Title\n@layout: bogus-name")
expect(slide_layout_short_name(a[0].layout)).to_equal("Blank")
expect(slide_layout_short_name(b[0].layout)).to_equal("Blank")
expect(slide_layout_short_name(c[0].layout)).to_equal("Blank")
```

</details>

#### excludes the @layout directive from title/body content

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val content = "Title\nBody\n@layout: section"
val slides = parse_deck(content)
var body_count = 0
for el in slides[0].elements:
    if el.id.starts_with("body"):
        body_count = body_count + 1
expect(body_count).to_equal(1)
```

</details>

#### serializes non-default layouts back to @layout: lines

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val slides = parse_deck("Only Title\n@layout: title-only\n---\nBig Section\n@layout: section")
val serialized = deck_to_text(slides)
expect(serialized).to_contain("@layout: title-only")
expect(serialized).to_contain("@layout: section")
```

</details>

#### emits no @layout line for the default layout

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val slides = parse_deck("Title\nBody")
val serialized = deck_to_text(slides)
expect(serialized.contains("@layout:")).to_be(false)
```

</details>

#### round-trips the full ground-truth deck exactly (levels + layouts)

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = "Agenda\n- Opening\n  - Welcome note\n    - Speaker intro\n- Closing\nPlain wrap-up line\n@notes: pace slowly\n---\nBreak Time\n@layout: title-only\n---\nPart Two\n@layout: section\n@transition: fade"
val slides = parse_deck(src)
expect(slides.len()).to_equal(3)
val serialized = deck_to_text(slides)
expect(serialized).to_equal(src)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 35 |
| Active scenarios | 35 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
