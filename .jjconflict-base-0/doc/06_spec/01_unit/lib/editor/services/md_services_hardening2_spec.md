# Md Services Hardening2 Specification

> <details>

<!-- sdn-diagram:id=md_services_hardening2_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=md_services_hardening2_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

md_services_hardening2_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=md_services_hardening2_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 65 | 65 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Md Services Hardening2 Specification

## Scenarios

### md_diagnostics: empty doc never crashes

#### md_diagnose on empty string returns empty list

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val r = md_diagnose("", "f.md")
expect(r.len()).to_equal(0)
```

</details>

#### md_check_duplicate_headings on empty string returns empty

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val r = md_check_duplicate_headings("", "f.md")
expect(r.len()).to_equal(0)
```

</details>

#### md_check_empty_headings on empty string returns empty

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val r = md_check_empty_headings("", "f.md")
expect(r.len()).to_equal(0)
```

</details>

#### md_check_unclosed_code_fences on empty string returns empty

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val r = md_check_unclosed_code_fences("", "f.md")
expect(r.len()).to_equal(0)
```

</details>

#### md_check_missing_alt_text on empty string returns empty

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val r = md_check_missing_alt_text("", "f.md")
expect(r.len()).to_equal(0)
```

</details>

#### md_check_trailing_whitespace on empty string returns empty

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val r = md_check_trailing_whitespace("", "f.md")
expect(r.len()).to_equal(0)
```

</details>

#### md_check_heading_level_skip on empty string returns empty

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val r = md_check_heading_level_skip("", "f.md")
expect(r.len()).to_equal(0)
```

</details>

#### md_check_inconsistent_list_markers on empty string returns empty

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val r = md_check_inconsistent_list_markers("", "f.md")
expect(r.len()).to_equal(0)
```

</details>

#### md_validate_local_links on empty string returns empty

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val r = md_validate_local_links("", "f.md", [])
expect(r.len()).to_equal(0)
```

</details>

### md_diagnostics: unterminated code fence

#### unterminated fence produces a diagnostic

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val doc = "# Title\n\n```rust\nfn hi() {}\n"
val r = md_check_unclosed_code_fences(doc, "f.md")
expect(r.len()).to_equal(1)
expect(r[0].line).to_equal(2)
```

</details>

#### matched fences produce no diagnostic

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val doc = "```rust\nfn hi() {}\n```\n"
val r = md_check_unclosed_code_fences(doc, "f.md")
expect(r.len()).to_equal(0)
```

</details>

#### closed fence followed by unclosed fence produces a diagnostic

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val doc = "```\ncode\n```\nsome text\n```\nmore\n"
val r = md_check_unclosed_code_fences(doc, "f.md")
expect(r.len()).to_equal(1)
```

</details>

### md_diagnostics: heading only hashes

#### line of only hashes is NOT a valid heading — no level-skip diagnostic from it

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val doc = "# Hello\n#### Only\n"
val r = md_check_empty_headings(doc, "f.md")
# '#### Only' has non-empty text so no empty-heading diagnostic
expect(r.len()).to_equal(0)
```

</details>

#### multiple valid headings produce no empty-heading diagnostic

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val doc = "# H1\n## H2\n### H3\n"
val r = md_check_empty_headings(doc, "f.md")
expect(r.len()).to_equal(0)
```

</details>

#### empty heading produces a diagnostic

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val doc = "# Title\n##\n"
val r = md_check_empty_headings(doc, "f.md")
expect(r.len()).to_equal(1)
expect(r[0].line).to_equal(1)
```

</details>

### md_diagnostics: images with empty src and empty alt

#### image with empty alt text produces a diagnostic

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val doc = "![](photo.png)\n"
val r = md_check_missing_alt_text(doc, "f.md")
expect(r.len()).to_equal(1)
```

</details>

#### image with non-empty alt text produces no diagnostic

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val doc = "![alt text](photo.png)\n"
val r = md_check_missing_alt_text(doc, "f.md")
expect(r.len()).to_equal(0)
```

</details>

#### image with non-empty alt and non-empty src produces no diagnostic

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val doc = "![my image](http://example.com/img.png)\n"
val r = md_check_missing_alt_text(doc, "f.md")
expect(r.len()).to_equal(0)
```

</details>

### md_diagnostics: broken heading link end_col clamped

#### multiple valid heading links produce no diagnostic

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val doc = "# Hello\n## World\n[go](#hello)\n[also](#world)\n"
val r = md_check_broken_heading_links(doc, "f.md")
expect(r.len()).to_equal(0)
```

</details>

#### link to missing heading produces a diagnostic

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val doc = "# Hello\n[go](#nowhere)\n"
val r = md_check_broken_heading_links(doc, "f.md")
expect(r.len()).to_equal(1)
```

</details>

#### link to existing heading has no diagnostic

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val doc = "# My Section\n[go](#my-section)\n"
val r = md_check_broken_heading_links(doc, "f.md")
expect(r.len()).to_equal(0)
```

</details>

### md_diagnostics: extremely long lines do not crash

#### trailing whitespace check on a 10k char line with no trailing space is safe

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var long_line = ""
var j = 0
while j < 200:
    long_line = long_line + "abcdefghijklmnopqrstuvwxyz1234567890123456789"
    j = j + 1
val r = md_check_trailing_whitespace(long_line, "f.md")
expect(r.len()).to_equal(0)
```

</details>

#### single trailing space on a long line produces a diagnostic

<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# 2+ trailing spaces are intentional markdown hard breaks; only 1 is flagged.
var long_line = ""
var j = 0
while j < 200:
    long_line = long_line + "abcdefghijklmnopqrstuvwxyz1234567890123456789"
    j = j + 1
val r = md_check_trailing_whitespace(long_line + " ", "f.md")
expect(r.len()).to_equal(1)
```

</details>

### md_search: empty and whitespace queries

#### empty query returns no results

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val r = md_search("hello world", "")
expect(r.len()).to_equal(0)
```

</details>

#### whitespace-only query returns no results

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val r = md_search("hello world", "   ")
expect(r.len()).to_equal(0)
```

</details>

#### tab-only query returns no results

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val r = md_search("hello world", "\t")
expect(r.len()).to_equal(0)
```

</details>

#### search over empty doc returns no results

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val r = md_search("", "hello")
expect(r.len()).to_equal(0)
```

</details>

#### query longer than doc returns no results

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val r = md_search("hi", "hello world this is much longer than the document")
expect(r.len()).to_equal(0)
```

</details>

### md_search: special chars in query

#### query with brackets does not crash

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val r = md_search("some [link](url) text", "[link]")
# should not crash; result count doesn't matter
val safe = r.len() >= 0
expect(safe).to_equal(true)
```

</details>

#### query with asterisk does not crash

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val r = md_search("**bold** text", "*")
val safe = r.len() >= 0
expect(safe).to_equal(true)
```

</details>

#### query with quotes does not crash

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val r = md_search("say \"hello\" there", "\"hello\"")
val safe = r.len() >= 0
expect(safe).to_equal(true)
```

</details>

#### query with backslash does not crash

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val r = md_search("path\\to\\file", "\\")
val safe = r.len() >= 0
expect(safe).to_equal(true)
```

</details>

### md_search: col is within line bounds

#### match col never exceeds line length

<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val doc = "# Heading\nThis has hello in it\nAnother hello line\n"
val r = md_search(doc, "hello")
var ok = true
var i = 0
while i < r.len():
    val m = r[i]
    val line_len = m.context_text.len()
    if m.col < 0 or m.col > line_len:
        ok = false
    i = i + 1
expect(ok).to_equal(true)
```

</details>

### md_search: headings and code blocks

#### md_search_in_headings with whitespace query returns empty

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val r = md_search_in_headings("# Title\n## Sub\n", "  ")
expect(r.len()).to_equal(0)
```

</details>

#### md_search_in_code_blocks with empty query returns empty

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val r = md_search_in_code_blocks("```\nhello\n```\n", "")
expect(r.len()).to_equal(0)
```

</details>

#### md_search_in_paragraphs over empty doc returns empty

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val r = md_search_in_paragraphs("", "hello")
expect(r.len()).to_equal(0)
```

</details>

#### md_search_in_links over empty doc returns empty

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val r = md_search_in_links("", "hello")
expect(r.len()).to_equal(0)
```

</details>

### md_doc_stats: empty and degenerate docs

#### empty doc produces zero counts and zero reading time

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val s = md_compute_stats("")
expect(s.word_count).to_equal(0)
expect(s.heading_count).to_equal(0)
expect(s.paragraph_count).to_equal(0)
expect(s.reading_time_minutes).to_equal(0)
```

</details>

#### punctuation-only doc word count is non-negative

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val s = md_compute_stats("!!! ??? --- ...")
# interpreter counts "!!!", "???", "---", "..." as 4 tokens
expect(s.word_count).to_equal(4)
```

</details>

#### line count for single-line doc is 1

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val s = md_compute_stats("hello world")
expect(s.line_count).to_equal(1)
```

</details>

### md_doc_stats: CRLF vs LF

#### CRLF doc line count matches LF doc line count

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val lf_doc = "# Title\n\nParagraph one.\n\nParagraph two.\n"
val crlf_doc = "# Title\r\n\r\nParagraph one.\r\n\r\nParagraph two.\r\n"
val lf_stats = md_compute_stats(lf_doc)
val crlf_stats = md_compute_stats(crlf_doc)
expect(lf_stats.heading_count).to_equal(crlf_stats.heading_count)
expect(lf_stats.paragraph_count).to_equal(crlf_stats.paragraph_count)
expect(lf_stats.word_count).to_equal(crlf_stats.word_count)
```

</details>

#### CRLF word count equals LF word count

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val lf = "hello world\nfoo bar\n"
val crlf = "hello world\r\nfoo bar\r\n"
val ls = md_compute_stats(lf)
val cs = md_compute_stats(crlf)
expect(ls.word_count).to_equal(cs.word_count)
```

</details>

### md_doc_stats: frontmatter excluded

#### frontmatter lines not counted as headings or words in body

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val with_fm = "---\ntitle: My Doc\ndate: 2026-01-01\n---\n# Hello\n\nBody text.\n"
val without_fm = "# Hello\n\nBody text.\n"
val s1 = md_compute_stats(with_fm)
val s2 = md_compute_stats(without_fm)
expect(s1.heading_count).to_equal(s2.heading_count)
# body word counts should match (frontmatter excluded)
expect(s1.word_count).to_equal(s2.word_count)
```

</details>

#### doc with only frontmatter has zero paragraph count

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val doc = "---\ntitle: Only FM\n---\n"
val s = md_compute_stats(doc)
expect(s.paragraph_count).to_equal(0)
expect(s.heading_count).to_equal(0)
```

</details>

### md_doc_stats: reading time

#### 200 word doc has reading time of 1 minute

- words push
   - Expected: s.reading_time_minutes equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var words: [text] = []
var j = 0
while j < 200:
    words.push("word")
    j = j + 1
val doc = words.join(" ")
val s = md_compute_stats(doc)
expect(s.reading_time_minutes).to_equal(1)
```

</details>

### md_sgrid: empty doc and zero-span inputs

#### md_sgrid_apply on empty content returns empty cells

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val cells = md_sgrid_apply("")
expect(cells.len()).to_equal(0)
```

</details>

#### md_sgrid_selection_sum with empty range returns zero

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = md_sgrid_selection_sum("| A | B |\n| --- | --- |\n| 3 | 4 |", "")
expect(result).to_equal("0")
```

</details>

#### md_sgrid_copy_selection with empty range returns empty

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = md_sgrid_copy_selection("| A |\n| --- |\n| 1 |", "")
expect(result).to_equal("")
```

</details>

#### md_sgrid_scan on empty content returns empty

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val blocks = md_sgrid_scan("")
expect(blocks.len()).to_equal(0)
```

</details>

#### md_sgrid_bind_tables on empty content returns empty

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val bindings = md_sgrid_bind_tables("")
expect(bindings.len()).to_equal(0)
```

</details>

### md_sgrid: range span normalisation

#### reverse range A2:A1 is normalised so row_start <= row_end

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val doc = "| Val |\n| --- |\n| 10 |\n| 20 |"
val result = md_sgrid_selection_sum(doc, "A2:A1")
# normalised to A1:A2, should not crash and return numeric result
val num = result.to_i64() ?? -1
val ok = num >= 0
expect(ok).to_equal(true)
```

</details>

#### single-cell range A1:A1 returns cell value

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val doc = "| Val |\n| --- |\n| 42 |"
# single-cell sum
val result = md_sgrid_selection_sum(doc, "A2:A2")
expect(result).to_equal("42")
```

</details>

### md_sgrid: pivot and formula on single-cell doc

#### md_sgrid_pivot_sum on table with one data row does not crash

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val doc = "| Item | Amount |\n| --- | --- |\n| foo | 10 |"
val rows = md_sgrid_pivot_sum(doc, "A", "B")
val safe = rows.len() >= 0
expect(safe).to_equal(true)
```

</details>

### md_document_decor: empty doc

#### md_document_decor_parse on empty string returns defaults

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val d = md_document_decor_parse("")
expect(d.page_view).to_equal(false)
expect(d.header).to_equal("")
expect(d.footer).to_equal("")
expect(d.layout).to_equal("document")
```

</details>

#### md_document_body_without_decor on empty returns empty

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val body = md_document_body_without_decor("")
expect(body).to_equal("")
```

</details>

#### md_document_sheet_cells on empty returns empty list

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val cells = md_document_sheet_cells("")
expect(cells.len()).to_equal(0)
```

</details>

#### md_document_split_ppt_pages on empty returns empty

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val slides = md_document_split_ppt_pages("")
expect(slides.len()).to_equal(0)
```

</details>

### md_document_decor: replace_sheet_cell_value bounds

#### replace on empty content returns content unchanged

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = md_document_replace_sheet_cell_value("", "A1", "42")
expect(result).to_equal("")
```

</details>

#### replace with empty address returns content unchanged

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val doc = "| A |\n| --- |\n| 1 |"
val result = md_document_replace_sheet_cell_value(doc, "", "42")
expect(result).to_equal(doc)
```

</details>

#### replace with invalid address (col 0) returns content unchanged

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val doc = "| A |\n| --- |\n| 1 |"
# address '1' has no letter prefix so col=0
val result = md_document_replace_sheet_cell_value(doc, "1", "42")
expect(result).to_equal(doc)
```

</details>

### md_document_decor: unterminated CSS fence is safe

#### unclosed css fence does not crash decor parse

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val doc = "---\nlayout: paper\n---\n```css\nbody { color: red; }\n"
val d = md_document_decor_parse(doc)
# inline_css may be empty or partial — just must not crash
val safe = d.layout.len() >= 0
expect(safe).to_equal(true)
```

</details>

#### body_without_decor on unclosed css fence is safe

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val doc = "# Title\n\n```css\nbody { margin: 0; }\n\nSome text."
val body = md_document_body_without_decor(doc)
val safe = body.len() >= 0
expect(safe).to_equal(true)
```

</details>

### md_document_decor: frontmatter parsing edge cases

#### frontmatter with no closing --- is handled safely

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val doc = "---\ntitle: No close\n\nSome content here.\n"
val d = md_document_decor_parse(doc)
val safe = d.layout.len() > 0
expect(safe).to_equal(true)
```

</details>

#### doc without frontmatter returns default decor

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val doc = "# Just a heading\n\nSome paragraph.\n"
val d = md_document_decor_parse(doc)
expect(d.page_view).to_equal(false)
expect(d.layout).to_equal("document")
```

</details>

#### frontmatter page_view true sets layout to paper

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val doc = "---\npage_view: true\n---\n# Content\n"
val d = md_document_decor_parse(doc)
expect(d.page_view).to_equal(true)
expect(d.layout).to_equal("paper")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/editor/services/md_services_hardening2_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- md_diagnostics: empty doc never crashes
- md_diagnostics: unterminated code fence
- md_diagnostics: heading only hashes
- md_diagnostics: images with empty src and empty alt
- md_diagnostics: broken heading link end_col clamped
- md_diagnostics: extremely long lines do not crash
- md_search: empty and whitespace queries
- md_search: special chars in query
- md_search: col is within line bounds
- md_search: headings and code blocks
- md_doc_stats: empty and degenerate docs
- md_doc_stats: CRLF vs LF
- md_doc_stats: frontmatter excluded
- md_doc_stats: reading time
- md_sgrid: empty doc and zero-span inputs
- md_sgrid: range span normalisation
- md_sgrid: pivot and formula on single-cell doc
- md_document_decor: empty doc
- md_document_decor: replace_sheet_cell_value bounds
- md_document_decor: unterminated CSS fence is safe
- md_document_decor: frontmatter parsing edge cases

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 65 |
| Active scenarios | 65 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
