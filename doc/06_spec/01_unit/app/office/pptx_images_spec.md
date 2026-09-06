# pptx_images_spec

> PPTX images: deck `![alt](path)` lines through export/import/HTML render.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 5 | 5 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# pptx_images_spec

PPTX images: deck `![alt](path)` lines through export/import/HTML render.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/01_unit/app/office/pptx_images_spec.spl` |
| Updated | 2026-08-18 |
| Generator | `simple spipe-docgen` (Simple) |

PPTX images: deck `![alt](path)` lines through export/import/HTML render.

Ground truth is structural, on the Word lane's 68-byte PNG fixture: the PNG
bytes land in ppt/media/image1.png (checked with our own zip reader AND the
system unzip on a scratchpad file), the slide rels wire rId3 to the media
part, the `<p:pic>` shape references it via r:embed, `unzip -t` exits 0, and
deck -> pptx -> deck preserves the exact `![alt](path)` line in position.
A missing file degrades to an alt-text textbox (no media part, no crash).
HTML render emits an `<img>` for existing files and a styled alt box
otherwise.

Lives in its own spec file: pptx_export_spec.spl already runs near the
per-file time budget (see pptx_layout_spec.spl's note).

## Scenarios

### PPTX images: export embeds PNG media

#### embeds a deck image as ppt/media/image1.png with wired rels and a p:pic

<details>
<summary>Executable SSpec</summary>

Runnable source: 29 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val png_path = _fixture_png_path()
val deck = parse_deck("Pics\nintro line\n![a tiny dot]({png_path})")
val pptx = deck_to_pptx_bytes(deck)
# media part exists (own zip reader) and holds the exact PNG bytes
val media = zip_extract(pptx, "ppt/media/image1.png")
expect(media != nil).to_be(true)
if val bytes = media:
    expect(bytes.len()).to_equal(68)
# slide rels wire rId3 -> the media part with the image rel type
val rels = zip_extract_text(pptx, "ppt/slides/_rels/slide1.xml.rels")
expect(rels).to_contain("Id=\"rId3\"")
expect(rels).to_contain("relationships/image")
expect(rels).to_contain("Target=\"../media/image1.png\"")
# slide part carries the pic shape referencing the rel, alt/src stashed
val slide1 = zip_extract_text(pptx, "ppt/slides/slide1.xml")
expect(slide1).to_contain("<p:pic>")
expect(slide1).to_contain("r:embed=\"rId3\"")
expect(slide1).to_contain("name=\"a tiny dot\"")
expect(slide1).to_contain("descr=\"{png_path}\"")
# png content-type Default present
val types = zip_extract_text(pptx, "[Content_Types].xml")
expect(types).to_contain("Extension=\"png\"")
# system unzip agrees: media listed, archive intact
val out_path = "{_SCRATCH}/pptx_images_spec.pptx"
File.write_bytes(out_path, pptx)
val list_result = run("unzip", ["-l", out_path])
expect(list_result.stdout).to_contain("ppt/media/image1.png")
val test_result = run("unzip", ["-t", out_path])
expect(test_result.exit_code).to_equal(0)
```

</details>

#### falls back to an alt-text textbox for a missing file (no media, no crash)

<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val deck = parse_deck("Pics\n![gone](/no/such/path/missing.png)")
val pptx = deck_to_pptx_bytes(deck)
val media = zip_extract(pptx, "ppt/media/image1.png")
expect(media).to_equal(nil)
val slide1 = zip_extract_text(pptx, "ppt/slides/slide1.xml")
expect(slide1.contains("<p:pic>")).to_be(false)
expect(slide1).to_contain("name=\"imageAlt\"")
expect(slide1).to_contain("<a:t>gone</a:t>")
```

</details>

### PPTX images: import round-trip

#### preserves the ![alt](path) line in position through deck -> pptx -> deck

<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val png_path = _fixture_png_path()
val src = "Pics\nbefore line\n![a tiny dot]({png_path})\nafter line"
val deck = parse_deck(src)
expect(deck_to_text(deck)).to_equal(src)
val pptx = deck_to_pptx_bytes(deck)
val deck2 = pptx_bytes_to_deck(pptx)
expect(deck2.len()).to_equal(1)
expect(deck_to_text(deck2)).to_equal(src)
```

</details>

### PPTX images: HTML render

#### renders an <img> with inline max-width for an existing file

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val png_path = _fixture_png_path()
val deck = parse_deck("Pics\n![a tiny dot]({png_path})")
val html = render_slide_html(deck[0])
expect(html).to_contain("<img src=\"{png_path}\"")
expect(html).to_contain("alt=\"a tiny dot\"")
expect(html).to_contain("max-width: 100%")
```

</details>

#### renders the alt text in a styled box when the file is missing

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val deck = parse_deck("Pics\n![gone](/no/such/path/missing.png)")
val html = render_slide_html(deck[0])
expect(html.contains("<img")).to_be(false)
expect(html).to_contain("border: 1px dashed")
expect(html).to_contain("gone")
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 5 |
| Active scenarios | 5 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
