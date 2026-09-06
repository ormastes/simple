# page_setup_spec

> Word page setup + section-break spec.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 13 | 13 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# page_setup_spec

Word page setup + section-break spec.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/01_unit/app/office/word/page_setup_spec.spl` |
| Updated | 2026-08-18 |
| Generator | `simple spipe-docgen` (Simple) |

Word page setup + section-break spec.

Hand-computed ground truths (twips, 1440/inch):
- US Letter portrait: 12240 x 15840, 1440 margin, 1 column.
- content_width_tw(letter) = 12240 - 2*1440 = 9360.
- landscape(letter): width 15840, height 12240, orientation "landscape".
- with_columns(letter, 2): column_width_tw = (9360 - 1*720) / 2 = 4320.

## Scenarios

### page_setup_letter: US Letter portrait defaults

#### is 12240 x 15840 twips, 1440 margin, portrait, 1 column

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val setup = page_setup_letter()
expect(setup.width_tw).to_equal(12240)
expect(setup.height_tw).to_equal(15840)
expect(setup.margin_tw).to_equal(1440)
expect(setup.orientation).to_equal("portrait")
expect(setup.columns).to_equal(1)
```

</details>

#### has content_width_tw = 9360 (width minus both margins)

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val setup = page_setup_letter()
expect(content_width_tw(setup)).to_equal(9360)
```

</details>

#### has column_width_tw = content width for a single column

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val setup = page_setup_letter()
expect(column_width_tw(setup)).to_equal(9360)
```

</details>

### page_setup_landscape: rotate a page setup

#### swaps width/height and sets orientation to landscape

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val letter = page_setup_letter()
val rotated = page_setup_landscape(letter)
expect(rotated.width_tw).to_equal(15840)
expect(rotated.height_tw).to_equal(12240)
expect(rotated.orientation).to_equal("landscape")
expect(rotated.margin_tw).to_equal(1440)
expect(rotated.columns).to_equal(1)
```

</details>

#### does not mutate the original setup

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val letter = page_setup_letter()
val rotated = page_setup_landscape(letter)
expect(letter.width_tw).to_equal(12240)
expect(letter.orientation).to_equal("portrait")
```

</details>

### page_setup_with_columns: multi-column layout

#### sets the column count and leaves other fields untouched

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val letter = page_setup_letter()
val two_col = page_setup_with_columns(letter, 2)
expect(two_col.columns).to_equal(2)
expect(two_col.width_tw).to_equal(12240)
expect(two_col.orientation).to_equal("portrait")
```

</details>

#### computes column_width_tw = (9360 - 720) / 2 = 4320

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val letter = page_setup_letter()
val two_col = page_setup_with_columns(letter, 2)
expect(column_width_tw(two_col)).to_equal(4320)
```

</details>

### sectpr_xml: Word <w:sectPr> fragment

#### contains pgSz with the section's width/height/orientation

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val letter = page_setup_letter()
val two_col = page_setup_with_columns(letter, 2)
val section = section_new("Body", two_col, "nextPage")
val xml = sectpr_xml(section)
expect(xml).to_contain("<w:pgSz w:w=\"12240\" w:h=\"15840\" w:orient=\"portrait\"/>")
```

</details>

#### contains pgMar with the uniform margin on all four sides

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val letter = page_setup_letter()
val section = section_new("Body", letter, "nextPage")
val xml = sectpr_xml(section)
expect(xml).to_contain("<w:pgMar w:top=\"1440\" w:bottom=\"1440\" w:left=\"1440\" w:right=\"1440\"/>")
```

</details>

#### contains cols with the section's column count

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val letter = page_setup_letter()
val two_col = page_setup_with_columns(letter, 2)
val section = section_new("Body", two_col, "nextPage")
val xml = sectpr_xml(section)
expect(xml).to_contain("<w:cols w:num=\"2\"/>")
```

</details>

#### contains the section break type

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val letter = page_setup_letter()
val section = section_new("Appendix", letter, "continuous")
val xml = sectpr_xml(section)
expect(xml).to_contain("<w:type w:val=\"continuous\"/>")
```

</details>

### sections_summary: one line per section

#### formats title, orientation, column count, and break kind

<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val letter = page_setup_letter()
val landscape_setup = page_setup_landscape(letter)
val two_col = page_setup_with_columns(landscape_setup, 3)
val sec1 = section_new("Cover", letter, "nextPage")
val sec2 = section_new("Body", two_col, "continuous")
val summary = sections_summary([sec1, sec2])
expect(summary.len()).to_equal(2)
expect(summary[0]).to_equal("Cover: portrait 1col break=nextPage")
expect(summary[1]).to_equal("Body: landscape 3col break=continuous")
```

</details>

### deliberate-fail probe (must be fixed to green before landing)

#### confirms column_width_tw is exact integer division with no remainder

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val letter = page_setup_letter()
val two_col = page_setup_with_columns(letter, 2)
# ground truth is 4320: (9360 - 720) / 2, exact integer division.
expect(column_width_tw(two_col)).to_equal(4320)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 13 |
| Active scenarios | 13 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
