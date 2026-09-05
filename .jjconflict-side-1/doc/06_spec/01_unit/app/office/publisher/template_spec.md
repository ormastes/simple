# Template Specification

> Tests covering publisher template: master construction, publisher template: apply_master_to_all, deliberate-fail probe (must stay green).

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 7 | 7 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Template Specification

## Scenarios

### publisher template: master construction

#### counts frames added to the master

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val master = _report_master()
expect(master_frame_count(master)).to_equal(2)
```

</details>

### publisher template: apply_master_to_all

#### gives each result page its own frames plus the master's frames

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val master = _report_master()
val pages = _content_pages()
val result = apply_master_to_all(master, pages, 1)
expect(page_frame_count(result[0])).to_equal(3)
expect(page_frame_count(result[1])).to_equal(3)
```

</details>

#### carries the master header text onto both pages

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val master = _report_master()
val pages = _content_pages()
val result = apply_master_to_all(master, pages, 1)
expect(frame_text(result[0], "hdr")).to_equal("Report")
expect(frame_text(result[1], "hdr")).to_equal("Report")
```

</details>

#### substitutes the # placeholder with each page's own number

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val master = _report_master()
val pages = _content_pages()
val result = apply_master_to_all(master, pages, 1)
expect(frame_text(result[0], "ftr")).to_equal("Page 1")
expect(frame_text(result[1], "ftr")).to_equal("Page 2")
```

</details>

#### preserves each page's own content frame text

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val master = _report_master()
val pages = _content_pages()
val result = apply_master_to_all(master, pages, 1)
expect(frame_text(result[0], "body1")).to_equal("")
expect(frame_text(result[1], "body2")).to_equal("")
```

</details>

#### renders the master header text into the page's HTML

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val master = _report_master()
val pages = _content_pages()
val result = apply_master_to_all(master, pages, 1)
val html = page_render_html(result[0])
expect(html).to_contain("Report")
```

</details>

### deliberate-fail probe (must stay green)

#### sanity-checks page-number substitution ground truth

<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val master = _report_master()
val pages = _content_pages()
val result = apply_master_to_all(master, pages, 1)
# Probe verified live: asserting "Page 1" for result[1]'s footer
# (should be page 2, not page 1) failed with "expected Page 2 to
# equal Page 1", confirming the harness executes this assertion.
# Correct ground truth: apply_master_to_all numbers sequentially
# from start_number, so result[1]'s footer is "Page 2".
expect(frame_text(result[1], "ftr")).to_equal("Page 2")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/01_unit/app/office/publisher/template_spec.spl` |
| Updated | 2026-08-18 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering publisher template: master construction, publisher template: apply_master_to_all, deliberate-fail probe (must stay green).
- publisher template: master construction
- publisher template: apply_master_to_all
- deliberate-fail probe (must stay green)

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 7 |
| Active scenarios | 7 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
