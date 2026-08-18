# pptx_export_spec

> PPTX export spec.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 10 | 10 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# pptx_export_spec

PPTX export spec.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/01_unit/app/office/pptx_export_spec.spl` |
| Updated | 2026-08-18 |
| Generator | `simple spipe-docgen` (Simple) |

PPTX export spec.

Decks build complete OPC packages: presentation + slide master/layout/theme
trio + one slide part per deck slide, with positioned text boxes in EMU and
escaped a:t runs. Validated through our own zip reader.

## Scenarios

### PPTX: deck export

#### packages all required OPC parts

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val deck = parse_deck("Intro\nWelcome\n---\nRoadmap")
val pptx = deck_to_pptx_bytes(deck)
val names = zip_entries(pptx)
expect(names.len()).to_equal(13)
expect(zip_extract_text(pptx, "[Content_Types].xml")).to_contain("presentationml.slide+xml")
expect(zip_extract_text(pptx, "ppt/presentation.xml")).to_contain("<p:sldIdLst>")
expect(zip_extract_text(pptx, "ppt/theme/theme1.xml")).to_contain("<a:clrScheme")
```

</details>

#### uses the SimpleOS default theme when the deck requests it

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val deck = parse_deck("Project Statistics\n@notes: simpleos-default-theme\nOwned inventory")
val pptx = deck_to_pptx_bytes(deck)
val theme = zip_extract_text(pptx, "ppt/theme/theme1.xml")
expect(theme).to_contain("name=\"SimpleOS Default\"")
expect(theme).to_contain("val=\"0058BC\"")
expect(theme).to_contain("typeface=\"Plus Jakarta Sans\"")
```

</details>

#### puts slide text into positioned a:t runs, escaped

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val deck = parse_deck("Title <1>\nBody & more")
val pptx = deck_to_pptx_bytes(deck)
val slide = zip_extract_text(pptx, "ppt/slides/slide1.xml")
expect(slide).to_contain("<a:t>Title &lt;1&gt;</a:t>")
expect(slide).to_contain("<a:t>Body &amp; more</a:t>")
expect(slide).to_contain("<a:off x=\"571500\"")
```

</details>

### PPTX: import round-trip

#### round-trips a deck through a real .pptx losslessly

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = "Intro\nWelcome\n---\nRoadmap\nQ3 goals"
val pptx = deck_to_pptx_bytes(parse_deck(src))
val deck2 = pptx_bytes_to_deck(pptx)
expect(deck2.len()).to_equal(2)
expect(deck_to_text(deck2)).to_equal(src)
```

</details>

#### extracts a:t runs in order with entities unescaped

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val texts = pptx_slide_texts("<p:sp><a:t>A &amp; B</a:t></p:sp><a:t>second</a:t>")
expect(texts.len()).to_equal(2)
expect(texts[0]).to_equal("A & B")
expect(texts[1]).to_equal("second")
```

</details>

### PPTX: speaker notes and transitions

#### writes a <p:transition> child into the slide XML

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var deck = parse_deck("Intro\nWelcome")
deck[0] = set_slide_transition(deck[0], "fade")
val pptx = deck_to_pptx_bytes(deck)
val slide_xml = zip_extract_text(pptx, "ppt/slides/slide1.xml")
expect(slide_xml).to_contain("<p:transition><p:fade/></p:transition>")
```

</details>

#### omits <p:transition> when no transition is set

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val deck = parse_deck("Intro\nWelcome")
val pptx = deck_to_pptx_bytes(deck)
val slide_xml = zip_extract_text(pptx, "ppt/slides/slide1.xml")
expect(slide_xml.contains("<p:transition>")).to_be(false)
```

</details>

#### adds a notesSlide OPC part when a slide has notes

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var deck = parse_deck("Intro\nWelcome")
deck[0] = set_slide_notes(deck[0], "Say hello warmly")
val pptx = deck_to_pptx_bytes(deck)
val notes_xml = zip_extract_text(pptx, "ppt/notesSlides/notesSlide1.xml")
expect(notes_xml).to_contain("Say hello warmly")
expect(zip_extract_text(pptx, "[Content_Types].xml")).to_contain("presentationml.notesSlide+xml")
expect(zip_extract_text(pptx, "ppt/slides/_rels/slide1.xml.rels")).to_contain("notesSlide")
```

</details>

#### omits notesSlide parts entirely when no slide has notes

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val deck = parse_deck("Intro\nWelcome\n---\nRoadmap")
val pptx = deck_to_pptx_bytes(deck)
expect(zip_extract_text(pptx, "ppt/notesSlides/notesSlide1.xml")).to_equal("")
expect(zip_extract_text(pptx, "[Content_Types].xml").contains("notesMaster")).to_be(false)
```

</details>

#### round-trips notes and transition through a real .pptx losslessly

<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var deck = parse_deck("Intro\nWelcome\n---\nRoadmap\nQ3 goals")
deck[0] = set_slide_notes(deck[0], "Opening remarks")
deck[0] = set_slide_transition(deck[0], "wipe")
deck[1] = set_slide_transition(deck[1], "push")
val pptx = deck_to_pptx_bytes(deck)
val deck2 = pptx_bytes_to_deck(pptx)
expect(deck2.len()).to_equal(2)
expect(deck2[0].notes).to_equal("Opening remarks")
expect(deck2[0].transition).to_equal("wipe")
expect(deck2[1].notes).to_equal("")
expect(deck2[1].transition).to_equal("push")
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 10 |
| Active scenarios | 10 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
