# Gallery Specification

> Tests covering publisher gallery: listing, publisher gallery: flyer template, publisher gallery: newsletter template, publisher gallery: brochure template, publisher gallery: unknown template fallback, publisher gallery: html rendering, deliberate-fail probe (must stay green).

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 17 | 17 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Gallery Specification

## Scenarios

### publisher gallery: listing

#### lists all three built-in templates

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val names = gallery_names()
expect(names).to_contain("flyer")
expect(names).to_contain("newsletter")
expect(names).to_contain("brochure")
```

</details>

#### gives the newsletter its exact preview summary

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(template_summary("newsletter")).to_equal("newsletter: title banner + 2 columns")
```

</details>

#### gives the flyer its exact preview summary

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(template_summary("flyer")).to_equal("flyer: title banner + single body frame")
```

</details>

#### gives the brochure its exact preview summary

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(template_summary("brochure")).to_equal("brochure: title banner + 3 columns")
```

</details>

### publisher gallery: flyer template

#### fills the title frame

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val page = build_template("flyer", "Big Sale", "Everything half off")
expect(frame_text(page, "title")).to_equal("Big Sale")
```

</details>

#### flows the body into the body frame

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val page = build_template("flyer", "Big Sale", "Everything half off")
expect(frame_text(page, "body")).to_contain("Everything")
```

</details>

#### has exactly title + body frames

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val page = build_template("flyer", "Big Sale", "Everything half off")
expect(page_frame_count(page)).to_equal(2)
```

</details>

### publisher gallery: newsletter template

#### fills the title banner

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val page = build_template("newsletter", "Town Herald", "News from around the block")
expect(frame_text(page, "title")).to_equal("Town Herald")
```

</details>

#### flows the body into the columns

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val page = build_template("newsletter", "Town Herald", "News from around the block")
expect(frame_text(page, "col0")).to_contain("News")
```

</details>

#### has exactly title + 2 column frames

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val page = build_template("newsletter", "Town Herald", "News from around the block")
expect(page_frame_count(page)).to_equal(3)
```

</details>

### publisher gallery: brochure template

#### fills the title banner

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val page = build_template("brochure", "Visit Us", "Come see our new location")
expect(frame_text(page, "title")).to_equal("Visit Us")
```

</details>

#### flows the body into the columns

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val page = build_template("brochure", "Visit Us", "Come see our new location")
expect(frame_text(page, "col0")).to_contain("Come")
```

</details>

#### has exactly title + 3 column frames

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val page = build_template("brochure", "Visit Us", "Come see our new location")
expect(page_frame_count(page)).to_equal(4)
```

</details>

### publisher gallery: unknown template fallback

#### fails soft to a title-only page

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val page = build_template("nonexistent", "Just A Title", "ignored body")
expect(frame_text(page, "title")).to_equal("Just A Title")
expect(page_frame_count(page)).to_equal(1)
```

</details>

#### gives unknown templates a generic summary

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(template_summary("nonexistent")).to_equal("unknown template: title only")
```

</details>

### publisher gallery: html rendering

#### renders the flyer with the title in the HTML

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val html = gallery_render_html("flyer", "Big Sale", "Everything half off")
expect(html).to_contain("Big Sale")
```

</details>

### deliberate-fail probe (must stay green)

#### sanity-checks the newsletter frame count ground truth

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val page = build_template("newsletter", "Town Herald", "News from around the block")
# Probe verified live: asserting 4 frames (brochure's count,
# not newsletter's) failed with "expected 3 to equal 4",
# confirming the harness executes this assertion. Correct
# ground truth: newsletter has col0 + col1 + title = 3 frames.
expect(page_frame_count(page)).to_equal(3)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/01_unit/app/office/publisher/gallery_spec.spl` |
| Updated | 2026-08-18 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering publisher gallery: listing, publisher gallery: flyer template, publisher gallery: newsletter template, publisher gallery: brochure template, publisher gallery: unknown template fallback, publisher gallery: html rendering, deliberate-fail probe (must stay green).
- publisher gallery: listing
- publisher gallery: flyer template
- publisher gallery: newsletter template
- publisher gallery: brochure template
- publisher gallery: unknown template fallback
- publisher gallery: html rendering
- deliberate-fail probe (must stay green)

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 17 |
| Active scenarios | 17 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
