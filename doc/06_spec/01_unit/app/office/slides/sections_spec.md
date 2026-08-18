# sections_spec

> Slide Sections + Summary Zoom spec.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 10 | 10 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# sections_spec

Slide Sections + Summary Zoom spec.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/01_unit/app/office/slides/sections_spec.spl` |
| Updated | 2026-08-18 |
| Generator | `simple spipe-docgen` (Simple) |

Slide Sections + Summary Zoom spec.

Verifies the deck-sections model in `app.office.slides.sections`: which
section owns a given slide index, the summary-zoom thumbnail lines derived
from section order, the `<p:sectionLst>` XML export, and reordering a
section within the section pane (`move_section`).

Ground-truth deck: Intro (slides 0-1, count 2), Body (slides 2-4, count 3),
Close (slide 5, count 1) — 6 slides total.

## Scenarios

### sections: totals and counts
_A 3-section, 6-slide deck reports the right totals._

#### sums slide_count across all sections to 6

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val ds = _sample_deck()
expect(total_slides(ds)).to_equal(6)
```

</details>

#### counts exactly 3 sections

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val ds = _sample_deck()
expect(section_count(ds)).to_equal(3)
```

</details>

### sections: section_of_slide lookup

#### maps slide 0 to Intro (first slide of the first section)

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val ds = _sample_deck()
expect(section_of_slide(ds, 0)).to_equal("Intro")
```

</details>

#### maps slide 3 to Body (middle of the Body range 2..5)

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val ds = _sample_deck()
expect(section_of_slide(ds, 3)).to_equal("Body")
```

</details>

#### maps slide 5 to Close (the last, single-slide section)

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val ds = _sample_deck()
expect(section_of_slide(ds, 5)).to_equal("Close")
```

</details>

#### maps an out-of-range slide index to the empty section name

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val ds = _sample_deck()
expect(section_of_slide(ds, 99)).to_equal("")
```

</details>

### sections: Summary Zoom targets

#### renders Intro -> slide 0, Body -> slide 2, Close -> slide 5 in order

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val ds = _sample_deck()
val targets = summary_zoom_targets(ds)
expect(targets[0]).to_equal("Intro -> slide 0")
expect(targets[1]).to_equal("Body -> slide 2")
expect(targets[2]).to_equal("Close -> slide 5")
```

</details>

### sections: PowerPoint XML export

#### contains the sectionLst wrapper and all three section names

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val ds = _sample_deck()
val xml = sections_to_xml(ds)
expect(xml).to_contain("<p:sectionLst")
expect(xml).to_contain("Intro")
expect(xml).to_contain("Body")
expect(xml).to_contain("Close")
```

</details>

### sections: move_section reorders the section pane

#### moves Close to the front, giving order Close, Intro, Body

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val ds = _sample_deck()
val reordered = move_section(ds, 2, 0)
val targets = summary_zoom_targets(reordered)
expect(targets[0]).to_equal("Close -> slide 5")
expect(targets[1]).to_equal("Intro -> slide 0")
expect(targets[2]).to_equal("Body -> slide 2")
```

</details>

### deliberate-fail probe (fixed to green)

#### has Body as the last entry after moving Close to the front

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val ds = _sample_deck()
val reordered = move_section(ds, 2, 0)
val targets = summary_zoom_targets(reordered)
expect(targets[2]).to_equal("Body -> slide 2")
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
