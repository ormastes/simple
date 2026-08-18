# Word Toc Specification

> Tests covering toc_entries: extract and number headings, toc_generate: insert TOC at document top, heading_numbering: prefix headings with numbers, complex workflow: toc + numbering.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 17 | 17 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Word Toc Specification

## Scenarios

### toc_entries: extract and number headings
_TOC entries are formatted as 'N Title' with hierarchical numbering._

#### extracts single heading

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val doc = _test_doc("# Introduction", "test")
val entries = toc_entries(doc, 3)
expect(entries.len()).to_equal(1)
expect(entries.get(0)).to_equal("1 Introduction")
```

</details>

#### numbers multiple level-1 headings

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val doc = _test_doc("# First\n\n# Second\n\n# Third", "test")
val entries = toc_entries(doc, 3)
expect(entries.len()).to_equal(3)
expect(entries.get(0)).to_equal("1 First")
expect(entries.get(1)).to_equal("2 Second")
expect(entries.get(2)).to_equal("3 Third")
```

</details>

#### numbers nested headings correctly

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val doc = _test_doc("# A\n\n## B\n\n## C\n\n# D", "test")
val entries = toc_entries(doc, 3)
expect(entries.len()).to_equal(4)
expect(entries.get(0)).to_equal("1 A")
expect(entries.get(1)).to_equal("1.1 B")
expect(entries.get(2)).to_equal("1.2 C")
expect(entries.get(3)).to_equal("2 D")
```

</details>

#### handles three-level nesting with auto-increment

<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val doc = _test_doc("# A\n\n## B\n\n## C\n\n# D\n\n### E\n\n## F", "test")
val entries = toc_entries(doc, 3)
expect(entries.len()).to_equal(6)
expect(entries.get(0)).to_equal("1 A")
expect(entries.get(1)).to_equal("1.1 B")
expect(entries.get(2)).to_equal("1.2 C")
expect(entries.get(3)).to_equal("2 D")
expect(entries.get(4)).to_equal("2.1.1 E")
expect(entries.get(5)).to_equal("2.2 F")
```

</details>

#### respects max_depth filtering

<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val doc = _test_doc("# A\n\n## B\n\n### C", "test")
val entries_depth_1 = toc_entries(doc, 1)
expect(entries_depth_1.len()).to_equal(1)
expect(entries_depth_1.get(0)).to_equal("1 A")

val entries_depth_2 = toc_entries(doc, 2)
expect(entries_depth_2.len()).to_equal(2)
expect(entries_depth_2.get(0)).to_equal("1 A")
expect(entries_depth_2.get(1)).to_equal("1.1 B")
```

</details>

#### ignores non-heading blocks

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val doc = _test_doc("# Title\n\nSome paragraph text.\n\n## Subtitle", "test")
val entries = toc_entries(doc, 3)
expect(entries.len()).to_equal(2)
expect(entries.get(0)).to_equal("1 Title")
expect(entries.get(1)).to_equal("1.1 Subtitle")
```

</details>

#### returns empty array when no headings

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val doc = _test_doc("Just a paragraph.\n\nAnd another.", "test")
val entries = toc_entries(doc, 3)
expect(entries.len()).to_equal(0)
```

</details>

### toc_generate: insert TOC at document top
_TOC document has title + entries + original blocks._

#### inserts TOC heading and entries at top

<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val doc = _test_doc("# Chapter 1\n\nContent here.", "test")
val toc_doc = toc_generate(doc, 3, "Contents")
# First block: TOC title
expect(toc_doc.blocks.get(0).kind).to_equal(BlockKind.Heading1)
val title_text = toc_doc.blocks.get(0).spans.get(0).text
expect(title_text).to_equal("Contents")
# Second block: TOC entry
expect(toc_doc.blocks.get(1).kind).to_equal(BlockKind.Paragraph)
val entry_text = toc_doc.blocks.get(1).spans.get(0).text
expect(entry_text).to_equal("1 Chapter 1")
# Third block: original content
expect(toc_doc.blocks.get(2).kind).to_equal(BlockKind.Heading1)
expect(toc_doc.blocks.len()).to_be_greater_than(3)
```

</details>

#### preserves original blocks after TOC

<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val original_md = "# A\n\nParagraph\n\n# B"
val doc = _test_doc(original_md, "test")
val toc_doc = toc_generate(doc, 3, "TOC")
# Original had 3 blocks (H1, Paragraph, H1) + new TOC (H1 title + 2 entries) = 6 blocks
expect(toc_doc.blocks.len()).to_equal(6)
# Last block should be the original "# B"
val last_block = toc_doc.blocks.get(toc_doc.blocks.len() - 1)
expect(last_block.kind).to_equal(BlockKind.Heading1)
```

</details>

#### respects max_depth in generated TOC

<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val doc = _test_doc("# A\n\n## B\n\n### C", "test")
val toc_doc = toc_generate(doc, 2, "Contents")
# Should have: title (1) + filtered entries (2) + originals (3) = 6 blocks
expect(toc_doc.blocks.len()).to_equal(6)
# Check entries are present
expect(toc_doc.blocks.get(1).spans.get(0).text).to_equal("1 A")
expect(toc_doc.blocks.get(2).spans.get(0).text).to_equal("1.1 B")
# C should not be in TOC entries but should be in original blocks
```

</details>

### heading_numbering: prefix headings with numbers
_heading_numbering returns a document where each heading is prefixed._

#### prefixes single heading

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val doc = _test_doc("# Introduction", "test")
val numbered = heading_numbering(doc)
expect(numbered.blocks.len()).to_equal(1)
val text = numbered.blocks.get(0).spans.get(0).text
expect(text).to_equal("1 Introduction")
```

</details>

#### prefixes multiple headings

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val doc = _test_doc("# First\n\n# Second", "test")
val numbered = heading_numbering(doc)
expect(numbered.blocks.get(0).spans.get(0).text).to_equal("1 First")
expect(numbered.blocks.get(1).spans.get(0).text).to_equal("2 Second")
```

</details>

#### prefixes nested headings

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val doc = _test_doc("# A\n\n## B\n\n## C\n\n# D", "test")
val numbered = heading_numbering(doc)
expect(numbered.blocks.get(0).spans.get(0).text).to_equal("1 A")
expect(numbered.blocks.get(1).spans.get(0).text).to_equal("1.1 B")
expect(numbered.blocks.get(2).spans.get(0).text).to_equal("1.2 C")
expect(numbered.blocks.get(3).spans.get(0).text).to_equal("2 D")
```

</details>

#### handles level-jump to level 3

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val doc = _test_doc("# A\n\n# D\n\n### E", "test")
val numbered = heading_numbering(doc)
expect(numbered.blocks.get(0).spans.get(0).text).to_equal("1 A")
expect(numbered.blocks.get(1).spans.get(0).text).to_equal("2 D")
expect(numbered.blocks.get(2).spans.get(0).text).to_equal("2.1.1 E")
```

</details>

#### preserves non-heading blocks

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val doc = _test_doc("# Title\n\nParagraph text.", "test")
val numbered = heading_numbering(doc)
expect(numbered.blocks.len()).to_equal(2)
expect(numbered.blocks.get(0).kind).to_equal(BlockKind.Heading1)
expect(numbered.blocks.get(1).kind).to_equal(BlockKind.Paragraph)
val para_text = numbered.blocks.get(1).spans.get(0).text
expect(para_text).to_equal("Paragraph text.")
```

</details>

#### round-trip: numbered document back to markdown preserves numbers

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val doc = _test_doc("# A\n\n## B", "test")
val numbered = heading_numbering(doc)
val md = document_to_markdown(numbered)
expect(md).to_contain("# 1 A")
expect(md).to_contain("## 1.1 B")
```

</details>

### complex workflow: toc + numbering
_Realistic workflow: number headings and generate TOC._

#### generates TOC and preserves original structure

<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val orig_md = "# Chapter 1\n\n## Section 1.1\n\nContent.\n\n## Section 1.2\n\n# Chapter 2"
val doc = _test_doc(orig_md, "report")
val toc_doc = toc_generate(doc, 3, "Table of Contents")

# Verify TOC entries
val toc_entry_1 = toc_doc.blocks.get(1).spans.get(0).text
val toc_entry_2 = toc_doc.blocks.get(2).spans.get(0).text
expect(toc_entry_1).to_equal("1 Chapter 1")
expect(toc_entry_2).to_equal("1.1 Section 1.1")

# Verify original structure is intact: last block should be original "Chapter 2"
val last_block = toc_doc.blocks.get(toc_doc.blocks.len() - 1)
expect(last_block.kind).to_equal(BlockKind.Heading1)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/01_unit/app/office/word_toc_spec.spl` |
| Updated | 2026-08-18 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering toc_entries: extract and number headings, toc_generate: insert TOC at document top, heading_numbering: prefix headings with numbers, complex workflow: toc + numbering.
- toc_entries: extract and number headings
- toc_generate: insert TOC at document top
- heading_numbering: prefix headings with numbers
- complex workflow: toc + numbering

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 17 |
| Active scenarios | 17 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
