# pptx_layout_spec

> PPTX bullet levels and slide layout variants.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 2 | 2 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# pptx_layout_spec

PPTX bullet levels and slide layout variants.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/01_unit/app/office/pptx_layout_spec.spl` |
| Updated | 2026-08-18 |
| Generator | `simple spipe-docgen` (Simple) |

PPTX bullet levels and slide layout variants.

Nested deck bullets export as `<a:pPr lvl=\"N\"><a:buChar/></a:pPr>` paragraph
properties (lvl omitted for level 0) and import back to indentation;
@layout: title-only|section map to alternate shape arrangements (centered
title / big centered title with a larger font size attr) marked by shape
names, round-tripping losslessly. Package integrity is validated with the
system `unzip -t`.

Lives in its own spec file (not pptx_export_spec.spl) because that file's
9 package-building cases already run ~60s and the test runner terminates a
file at its per-file budget — added cases there were killed mid-run.

## Scenarios

### PPTX: bullet levels and slide layouts

#### exports bullet lvl attrs and layout arrangements (3-slide ground truth)

<details>
<summary>Executable SSpec</summary>

Runnable source: 22 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = "Agenda\n- Opening\n  - Welcome note\n    - Speaker intro\n- Closing\nPlain wrap-up line\n@notes: pace slowly\n---\nBreak Time\n@layout: title-only\n---\nPart Two\n@layout: section\n@transition: fade"
val deck = parse_deck(src)
val pptx = deck_to_pptx_bytes(deck)
# Slide 1 (default layout): nested bullet levels, lvl omitted for 0
val slide1 = zip_extract_text(pptx, "ppt/slides/slide1.xml")
expect(slide1).to_contain("lvl=\"1\"")
expect(slide1).to_contain("lvl=\"2\"")
expect(slide1.contains("lvl=\"0\"")).to_be(false)
expect(slide1).to_contain("<a:pPr><a:buChar char=\"-\"/></a:pPr>")
# Title and plain body paragraphs carry no bullet properties
expect(slide1).to_contain("<a:p><a:r><a:t>Agenda</a:t>")
expect(slide1).to_contain("<a:p><a:r><a:t>Plain wrap-up line</a:t>")
# Slide 2: title-only = just a centered title shape
val slide2 = zip_extract_text(pptx, "ppt/slides/slide2.xml")
expect(slide2).to_contain("name=\"ctrTitle\"")
val texts2 = pptx_slide_texts(slide2)
expect(texts2.len()).to_equal(1)
expect(texts2[0]).to_equal("Break Time")
# Slide 3: section = big centered title with larger font size attr
val slide3 = zip_extract_text(pptx, "ppt/slides/slide3.xml")
expect(slide3).to_contain("name=\"sectionTitle\"")
expect(slide3).to_contain("<a:rPr sz=\"4400\"/>")
```

</details>

#### round-trips levels and layouts losslessly and passes system unzip -t

<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = "Agenda\n- Opening\n  - Welcome note\n    - Speaker intro\n- Closing\nPlain wrap-up line\n@notes: pace slowly\n---\nBreak Time\n@layout: title-only\n---\nPart Two\n@layout: section\n@transition: fade"
val deck = parse_deck(src)
expect(deck_to_text(deck)).to_equal(src)
val pptx = deck_to_pptx_bytes(deck)
val deck2 = pptx_bytes_to_deck(pptx)
expect(deck2.len()).to_equal(3)
expect(deck_to_text(deck2)).to_equal(src)
expect(deck2[0].notes).to_equal("pace slowly")
expect(deck2[2].transition).to_equal("fade")
val out_path = "/tmp/claude-1000/-home-ormastes-dev-pub-simple/de80534b-2c68-466d-a211-9ec2529fed18/scratchpad/pptx_bullets_spec.pptx"
File.write_bytes(out_path, pptx)
val test_result = run("unzip", ["-t", out_path])
expect(test_result.exit_code).to_equal(0)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 2 |
| Active scenarios | 2 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
