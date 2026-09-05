# Word Edit Ops Specification

> Tests covering document find: locate text occurrences, document replace: modify text in spans, document plain text: extract unformatted text, document statistics: word/character/paragraph counts, round-trip workflow: find-replace-verify.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 26 | 26 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Word Edit Ops Specification

## Scenarios

### document find: locate text occurrences
_Find returns hit locations as 'blockIndex:charOffset' strings._

#### finds a single occurrence in a paragraph

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val doc = _test_doc("Hello world", "test")
val hits = document_find(doc, "world")
expect(hits.len()).to_equal(1)
expect(hits.get(0)).to_equal("0:6")
```

</details>

#### finds multiple occurrences in the same block

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val doc = _test_doc("hello hello hello", "test")
val hits = document_find(doc, "hello")
expect(hits.len()).to_equal(3)
expect(hits.get(0)).to_equal("0:0")
expect(hits.get(1)).to_equal("0:6")
expect(hits.get(2)).to_equal("0:12")
```

</details>

#### finds occurrences across multiple blocks

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val doc = _test_doc("Find me\n\nFind me again", "test")
val hits = document_find(doc, "Find")
expect(hits.len()).to_equal(2)
expect(hits.get(0)).to_equal("0:0")
expect(hits.get(1)).to_equal("1:0")
```

</details>

#### is case-sensitive

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val doc = _test_doc("Find FIND find", "test")
val hits = document_find(doc, "find")
expect(hits.len()).to_equal(1)
expect(hits.get(0)).to_equal("0:10")
```

</details>

#### returns empty array when text not found

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val doc = _test_doc("hello world", "test")
val hits = document_find(doc, "xyz")
expect(hits.len()).to_equal(0)
```

</details>

### document replace: modify text in spans
_Replace all occurrences; preserves styles and block structure._

#### replaces a single occurrence

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val doc = _test_doc("Hello world", "test")
val replaced = document_replace(doc, "world", "Simple")
val text = document_to_markdown(replaced)
expect(text).to_contain("Hello Simple")
expect(text.contains("world")).to_be(false)
```

</details>

#### replaces multiple occurrences

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val doc = _test_doc("cat cat cat", "test")
val replaced = document_replace(doc, "cat", "dog")
val text = document_to_markdown(replaced)
expect(text).to_equal("dog dog dog")
```

</details>

#### preserves span styles during replacement

<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val doc = RichDocument(title: "test", blocks: [_para_mixed("prefix ", "bold", " suffix")], comments: [], revisions: [])
val replaced = document_replace(doc, "prefix", "new")
val block = replaced.blocks.get(0)
val span0 = block.spans.get(0)
expect(span0.text).to_equal("new ")
expect(span0.style).to_equal(InlineStyle.Normal)
val span1 = block.spans.get(1)
expect(span1.style).to_equal(InlineStyle.Bold)
```

</details>

#### replaces text within bold spans

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val doc = RichDocument(title: "test", blocks: [_para_mixed("", "find me", "")], comments: [], revisions: [])
val replaced = document_replace(doc, "find", "found")
val span = replaced.blocks.get(0).spans.get(1)
expect(span.text).to_equal("found me")
expect(span.style).to_equal(InlineStyle.Bold)
```

</details>

#### replaces across block boundaries (separately in each block)

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val doc = _test_doc("The cat\n\nThe dog", "test")
val replaced = document_replace(doc, "The", "A")
val text = document_to_markdown(replaced)
expect(text).to_contain("A cat")
expect(text).to_contain("A dog")
```

</details>

#### returns unchanged document when needle not found

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val doc = _test_doc("hello world", "test")
val replaced = document_replace(doc, "xyz", "abc")
val text = document_to_markdown(replaced)
expect(text).to_equal("hello world")
```

</details>

#### handles empty needle (returns unchanged)

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val doc = _test_doc("hello", "test")
val replaced = document_replace(doc, "", "x")
val text = document_to_markdown(replaced)
expect(text).to_equal("hello")
```

</details>

### document plain text: extract unformatted text
_Plain text drops all markup, prefixes bullets, removes heading markers._

#### joins blocks with newlines

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val doc = _test_doc("First\n\nSecond", "test")
val plain = document_plain_text(doc)
expect(plain).to_contain("First")
expect(plain).to_contain("Second")
# Should have a newline between them
expect(plain.contains("First\n")).to_be(true)
```

</details>

#### drops inline styles (bold/italic/code)

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val doc = _test_doc("This **is bold** and *italic*.", "test")
val plain = document_plain_text(doc)
expect(plain).to_equal("This is bold and italic.")
```

</details>

#### prefixes bullet items with '- '

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val doc = _test_doc("- item one\n- item two", "test")
val plain = document_plain_text(doc)
expect(plain).to_contain("- item one")
expect(plain).to_contain("- item two")
```

</details>

#### removes heading markers

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val doc = _test_doc("# Title\n\n## Subtitle", "test")
val plain = document_plain_text(doc)
expect(plain).to_contain("Title")
expect(plain).to_contain("Subtitle")
expect(plain.contains("#")).to_be(false)
```

</details>

### document statistics: word/character/paragraph counts
_Counts are accurate for real documents._

#### counts words correctly (whitespace-separated tokens)

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val doc = _test_doc("one two three", "test")
val count = document_word_count_new(doc)
expect(count).to_equal(3)
```

</details>

#### counts words in multiple paragraphs

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val doc = _test_doc("one two\n\nthree four five", "test")
val count = document_word_count_new(doc)
expect(count).to_equal(5)
```

</details>

#### ignores extra whitespace when counting words

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val doc = _test_doc("one  two   three", "test")
val count = document_word_count_new(doc)
expect(count).to_equal(3)
```

</details>

#### counts characters (text without markup)

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val doc = _test_doc("hello world", "test")
val count = document_character_count(doc)
# "hello world" = 11 characters
expect(count).to_equal(11)
```

</details>

#### counts characters across multiple blocks

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val doc = _test_doc("five\n\nfour", "test")
val count = document_character_count(doc)
# "five" = 4, "four" = 4, total 8
expect(count).to_equal(8)
```

</details>

#### counts paragraphs (non-empty text blocks)

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val doc = _test_doc("para 1\n\npara 2\n\npara 3", "test")
val count = document_paragraph_count(doc)
expect(count).to_equal(3)
```

</details>

#### excludes empty blocks from paragraph count

<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val doc = RichDocument(title: "test", blocks: [
    _para("text"),
    _para(""),
    _para("more")
], comments: [], revisions: [])
val count = document_paragraph_count(doc)
# Only 2 non-empty blocks
expect(count).to_equal(2)
```

</details>

#### returns all stats via document_stats struct

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val doc = _test_doc("one two\n\nthree four", "test")
val stats = document_stats(doc)
expect(stats.words).to_equal(4)
expect(stats.paragraphs).to_equal(2)
expect(stats.characters).to_be_greater_than(0)
```

</details>

### round-trip workflow: find-replace-verify
_Realistic workflow: find text, replace it, verify result._

#### replaces **bold** text and keeps the bold markup

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val orig = "This **bold** word"
val doc = _test_doc(orig, "test")
val replaced = document_replace(doc, "bold", "EMPHASIZED")
val markdown = document_to_markdown(replaced)
expect(markdown).to_contain("**EMPHASIZED**")
expect(markdown.contains("**bold**")).to_be(false)
```

</details>

#### finds and replaces multiple instances, counts remain accurate

<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val orig = "cat and cat and cat"
val doc = _test_doc(orig, "test")
val before_words = document_word_count_new(doc)
val replaced = document_replace(doc, "cat", "dog")
val after_words = document_word_count_new(replaced)
# Word count doesn't change (same number of words)
expect(before_words).to_equal(after_words)
val markdown = document_to_markdown(replaced)
expect(markdown.contains("cat")).to_be(false)
expect(markdown).to_contain("dog and dog and dog")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/01_unit/app/office/word_edit_ops_spec.spl` |
| Updated | 2026-08-18 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering document find: locate text occurrences, document replace: modify text in spans, document plain text: extract unformatted text, document statistics: word/character/paragraph counts, round-trip workflow: find-replace-verify.
- document find: locate text occurrences
- document replace: modify text in spans
- document plain text: extract unformatted text
- document statistics: word/character/paragraph counts
- round-trip workflow: find-replace-verify

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 26 |
| Active scenarios | 26 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
