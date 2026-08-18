# Catalog Merge Specification

> Tests covering catalog merge: tile substitution, catalog merge: tile count, catalog merge: grid placement, catalog merge: html rendering, deliberate-fail probe (must stay green).

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 9 | 9 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Catalog Merge Specification

## Scenarios

### catalog merge: tile substitution

#### fills a tile's placeholders from the parallel field values

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val filled = merge_tile(_template(), FIELD_NAMES, ["Apple", "2"])
expect(filled).to_equal("Apple\n$2")
```

</details>

#### fills a different record's values into the same template

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val filled = merge_tile(_template(), FIELD_NAMES, ["Banana", "1"])
expect(filled).to_equal("Banana\n$1")
```

</details>

### catalog merge: tile count

#### produces exactly one frame per data record

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val page = catalog_merge(_template(), 400, 200, 2, FIELD_NAMES, RECORDS)
expect(catalog_tile_count(page)).to_equal(3)
```

</details>

### catalog merge: grid placement

#### places record 0 in the top-left tile

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val page = catalog_merge(_template(), 400, 200, 2, FIELD_NAMES, RECORDS)
expect(frame_text(page, "tile0")).to_contain("Apple")
```

</details>

#### places record 1 in column 1 of row 0 (x=200, y=0)

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val html = catalog_render_html(_template(), 400, 200, 2, FIELD_NAMES, RECORDS)
expect(html).to_contain("Banana")
expect(html).to_contain("left:200px;top:0px")
```

</details>

#### places record 2 in column 0 of row 1 (x=0, y=100)

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val page = catalog_merge(_template(), 400, 200, 2, FIELD_NAMES, RECORDS)
expect(frame_text(page, "tile2")).to_contain("Cherry")
```

</details>

#### renders record 2's tile at the row-1 offset in html

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val html = catalog_render_html(_template(), 400, 200, 2, FIELD_NAMES, RECORDS)
expect(html).to_contain("left:0px;top:100px")
```

</details>

### catalog merge: html rendering

#### includes every record's fields in the rendered catalog page

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val html = catalog_render_html(_template(), 400, 200, 2, FIELD_NAMES, RECORDS)
expect(html).to_contain("Apple")
expect(html).to_contain("Banana")
expect(html).to_contain("Cherry")
```

</details>

### deliberate-fail probe (must stay green)

#### sanity-checks the hand-computed substitution ground truth

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val filled = merge_tile(_template(), FIELD_NAMES, ["Apple", "2"])
# Probe verified live: asserting filled equals "Apple\n$1"
# (record 1's price instead of record 0's) failed with a
# mismatch, confirming the harness executes this assertion.
# Correct ground truth: record 0's own price is "$2".
expect(filled).to_equal("Apple\n$2")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/01_unit/app/office/publisher/catalog_merge_spec.spl` |
| Updated | 2026-08-18 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering catalog merge: tile substitution, catalog merge: tile count, catalog merge: grid placement, catalog merge: html rendering, deliberate-fail probe (must stay green).
- catalog merge: tile substitution
- catalog merge: tile count
- catalog merge: grid placement
- catalog merge: html rendering
- deliberate-fail probe (must stay green)

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 9 |
| Active scenarios | 9 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
