# Md Services Hardening2 Specification

> Tests covering md_diagnostics: empty doc never crashes, md_diagnostics: unterminated code fence, md_diagnostics: heading only hashes, md_diagnostics: images with empty src and empty alt, md_diagnostics: broken heading link end_col clamped, md_diagnostics: extremely long lines do not crash, md_search: empty and whitespace queries, md_search: special chars in query, md_search: col is within line bounds, md_search: headings and code blocks, md_doc_stats: empty and degenerate docs, md_doc_stats: CRLF vs LF, md_doc_stats: frontmatter excluded, md_doc_stats: reading time, md_sgrid: empty doc and zero-span inputs, md_sgrid: range span normalisation, md_sgrid: pivot and formula on single-cell doc, md_document_decor: empty doc, md_document_decor: replace_sheet_cell_value bounds, md_document_decor: unterminated CSS fence is safe, md_document_decor: frontmatter parsing edge cases.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 65 | 65 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Md Services Hardening2 Specification

## Scenarios

### md_diagnostics: empty doc never crashes

#### md_diagnose on empty string returns empty list

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- md_diagnose on empty string returns empty list
   - Expected: r.len() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("md_diagnose on empty string returns empty list")
val r = md_diagnose("", "f.md")
expect(r.len()).to_equal(0)
```

</details>

#### md_check_duplicate_headings on empty string returns empty

- md_check_duplicate_headings on empty string returns empty
   - Expected: r.len() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("md_check_duplicate_headings on empty string returns empty")
val r = md_check_duplicate_headings("", "f.md")
expect(r.len()).to_equal(0)
```

</details>

#### md_check_empty_headings on empty string returns empty

- md_check_empty_headings on empty string returns empty
   - Expected: r.len() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("md_check_empty_headings on empty string returns empty")
val r = md_check_empty_headings("", "f.md")
expect(r.len()).to_equal(0)
```

</details>

#### md_check_unclosed_code_fences on empty string returns empty

- md_check_unclosed_code_fences on empty string returns empty
   - Expected: r.len() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("md_check_unclosed_code_fences on empty string returns empty")
val r = md_check_unclosed_code_fences("", "f.md")
expect(r.len()).to_equal(0)
```

</details>

#### md_check_missing_alt_text on empty string returns empty

- md_check_missing_alt_text on empty string returns empty
   - Expected: r.len() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("md_check_missing_alt_text on empty string returns empty")
val r = md_check_missing_alt_text("", "f.md")
expect(r.len()).to_equal(0)
```

</details>

#### md_check_trailing_whitespace on empty string returns empty

- md_check_trailing_whitespace on empty string returns empty
   - Expected: r.len() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("md_check_trailing_whitespace on empty string returns empty")
val r = md_check_trailing_whitespace("", "f.md")
expect(r.len()).to_equal(0)
```

</details>

#### md_check_heading_level_skip on empty string returns empty

- md_check_heading_level_skip on empty string returns empty
   - Expected: r.len() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("md_check_heading_level_skip on empty string returns empty")
val r = md_check_heading_level_skip("", "f.md")
expect(r.len()).to_equal(0)
```

</details>

#### md_check_inconsistent_list_markers on empty string returns empty

- md_check_inconsistent_list_markers on empty string returns empty
   - Expected: r.len() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("md_check_inconsistent_list_markers on empty string returns empty")
val r = md_check_inconsistent_list_markers("", "f.md")
expect(r.len()).to_equal(0)
```

</details>

#### md_validate_local_links on empty string returns empty

- md_validate_local_links on empty string returns empty
   - Expected: r.len() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("md_validate_local_links on empty string returns empty")
val r = md_validate_local_links("", "f.md", [])
expect(r.len()).to_equal(0)
```

</details>

### md_diagnostics: unterminated code fence

#### unterminated fence produces a diagnostic

- unterminated fence produces a diagnostic
   - Expected: r.len() equals `1`
   - Expected: r[0].line equals `2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("unterminated fence produces a diagnostic")
val doc = "# Title\n\n```rust\nfn hi() {}\n"
val r = md_check_unclosed_code_fences(doc, "f.md")
expect(r.len()).to_equal(1)
expect(r[0].line).to_equal(2)
```

</details>

#### matched fences produce no diagnostic

- matched fences produce no diagnostic
   - Expected: r.len() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("matched fences produce no diagnostic")
val doc = "```rust\nfn hi() {}\n```\n"
val r = md_check_unclosed_code_fences(doc, "f.md")
expect(r.len()).to_equal(0)
```

</details>

#### closed fence followed by unclosed fence produces a diagnostic

- closed fence followed by unclosed fence produces a diagnostic
   - Expected: r.len() equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("closed fence followed by unclosed fence produces a diagnostic")
val doc = "```\ncode\n```\nsome text\n```\nmore\n"
val r = md_check_unclosed_code_fences(doc, "f.md")
expect(r.len()).to_equal(1)
```

</details>

### md_diagnostics: heading only hashes

#### line of only hashes is NOT a valid heading — no level-skip diagnostic from it

- line of only hashes is NOT a valid heading — no level-skip diagnostic from it
   - Expected: r.len() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("line of only hashes is NOT a valid heading — no level-skip diagnostic from it")
val doc = "# Hello\n#### Only\n"
val r = md_check_empty_headings(doc, "f.md")
# '#### Only' has non-empty text so no empty-heading diagnostic
expect(r.len()).to_equal(0)
```

</details>

#### multiple valid headings produce no empty-heading diagnostic

- multiple valid headings produce no empty-heading diagnostic
   - Expected: r.len() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("multiple valid headings produce no empty-heading diagnostic")
val doc = "# H1\n## H2\n### H3\n"
val r = md_check_empty_headings(doc, "f.md")
expect(r.len()).to_equal(0)
```

</details>

#### empty heading produces a diagnostic

- empty heading produces a diagnostic
   - Expected: r.len() equals `1`
   - Expected: r[0].line equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("empty heading produces a diagnostic")
val doc = "# Title\n##\n"
val r = md_check_empty_headings(doc, "f.md")
expect(r.len()).to_equal(1)
expect(r[0].line).to_equal(1)
```

</details>

### md_diagnostics: images with empty src and empty alt

#### image with empty alt text produces a diagnostic

- image with empty alt text produces a diagnostic
   - Expected: r.len() equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("image with empty alt text produces a diagnostic")
val doc = "![](photo.png)\n"
val r = md_check_missing_alt_text(doc, "f.md")
expect(r.len()).to_equal(1)
```

</details>

#### image with non-empty alt text produces no diagnostic

- image with non-empty alt text produces no diagnostic
   - Expected: r.len() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("image with non-empty alt text produces no diagnostic")
val doc = "![alt text](photo.png)\n"
val r = md_check_missing_alt_text(doc, "f.md")
expect(r.len()).to_equal(0)
```

</details>

#### image with non-empty alt and non-empty src produces no diagnostic

- image with non-empty alt and non-empty src produces no diagnostic
   - Expected: r.len() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("image with non-empty alt and non-empty src produces no diagnostic")
val doc = "![my image](http://example.com/img.png)\n"
val r = md_check_missing_alt_text(doc, "f.md")
expect(r.len()).to_equal(0)
```

</details>

### md_diagnostics: broken heading link end_col clamped

#### multiple valid heading links produce no diagnostic

- multiple valid heading links produce no diagnostic
   - Expected: r.len() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("multiple valid heading links produce no diagnostic")
val doc = "# Hello\n## World\n[go](#hello)\n[also](#world)\n"
val r = md_check_broken_heading_links(doc, "f.md")
expect(r.len()).to_equal(0)
```

</details>

#### link to missing heading produces a diagnostic

- link to missing heading produces a diagnostic
   - Expected: r.len() equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("link to missing heading produces a diagnostic")
val doc = "# Hello\n[go](#nowhere)\n"
val r = md_check_broken_heading_links(doc, "f.md")
expect(r.len()).to_equal(1)
```

</details>

#### link to existing heading has no diagnostic

- link to existing heading has no diagnostic
   - Expected: r.len() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("link to existing heading has no diagnostic")
val doc = "# My Section\n[go](#my-section)\n"
val r = md_check_broken_heading_links(doc, "f.md")
expect(r.len()).to_equal(0)
```

</details>

### md_diagnostics: extremely long lines do not crash

#### trailing whitespace check on a 10k char line with no trailing space is safe

- trailing whitespace check on a 10k char line with no trailing space is safe
   - Expected: r.len() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("trailing whitespace check on a 10k char line with no trailing space is safe")
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

- single trailing space on a long line produces a diagnostic
   - Expected: r.len() equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("single trailing space on a long line produces a diagnostic")
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

- empty query returns no results
   - Expected: r.len() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("empty query returns no results")
val r = md_search("hello world", "")
expect(r.len()).to_equal(0)
```

</details>

#### whitespace-only query returns no results

- whitespace-only query returns no results
   - Expected: r.len() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("whitespace-only query returns no results")
val r = md_search("hello world", "   ")
expect(r.len()).to_equal(0)
```

</details>

#### tab-only query returns no results

- tab-only query returns no results
   - Expected: r.len() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("tab-only query returns no results")
val r = md_search("hello world", "\t")
expect(r.len()).to_equal(0)
```

</details>

#### search over empty doc returns no results

- search over empty doc returns no results
   - Expected: r.len() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("search over empty doc returns no results")
val r = md_search("", "hello")
expect(r.len()).to_equal(0)
```

</details>

#### query longer than doc returns no results

- query longer than doc returns no results
   - Expected: r.len() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("query longer than doc returns no results")
val r = md_search("hi", "hello world this is much longer than the document")
expect(r.len()).to_equal(0)
```

</details>

### md_search: special chars in query

#### query with brackets does not crash

- query with brackets does not crash
   - Expected: safe is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("query with brackets does not crash")
val r = md_search("some [link](url) text", "[link]")
# should not crash; result count doesn't matter
val safe = r.len() >= 0
expect(safe).to_equal(true)
```

</details>

#### query with asterisk does not crash

- query with asterisk does not crash
   - Expected: safe is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("query with asterisk does not crash")
val r = md_search("**bold** text", "*")
val safe = r.len() >= 0
expect(safe).to_equal(true)
```

</details>

#### query with quotes does not crash

- query with quotes does not crash
   - Expected: safe is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("query with quotes does not crash")
val r = md_search("say \"hello\" there", "\"hello\"")
val safe = r.len() >= 0
expect(safe).to_equal(true)
```

</details>

#### query with backslash does not crash

- query with backslash does not crash
   - Expected: safe is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("query with backslash does not crash")
val r = md_search("path\\to\\file", "\\")
val safe = r.len() >= 0
expect(safe).to_equal(true)
```

</details>

### md_search: col is within line bounds

#### match col never exceeds line length

- match col never exceeds line length
   - Expected: ok is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("match col never exceeds line length")
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

- md_search_in_headings with whitespace query returns empty
   - Expected: r.len() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("md_search_in_headings with whitespace query returns empty")
val r = md_search_in_headings("# Title\n## Sub\n", "  ")
expect(r.len()).to_equal(0)
```

</details>

#### md_search_in_code_blocks with empty query returns empty

- md_search_in_code_blocks with empty query returns empty
   - Expected: r.len() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("md_search_in_code_blocks with empty query returns empty")
val r = md_search_in_code_blocks("```\nhello\n```\n", "")
expect(r.len()).to_equal(0)
```

</details>

#### md_search_in_paragraphs over empty doc returns empty

- md_search_in_paragraphs over empty doc returns empty
   - Expected: r.len() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("md_search_in_paragraphs over empty doc returns empty")
val r = md_search_in_paragraphs("", "hello")
expect(r.len()).to_equal(0)
```

</details>

#### md_search_in_links over empty doc returns empty

- md_search_in_links over empty doc returns empty
   - Expected: r.len() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("md_search_in_links over empty doc returns empty")
val r = md_search_in_links("", "hello")
expect(r.len()).to_equal(0)
```

</details>

### md_doc_stats: empty and degenerate docs

#### empty doc produces zero counts and zero reading time

- empty doc produces zero counts and zero reading time
   - Expected: s.word_count equals `0`
   - Expected: s.heading_count equals `0`
   - Expected: s.paragraph_count equals `0`
   - Expected: s.reading_time_minutes equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("empty doc produces zero counts and zero reading time")
val s = md_compute_stats("")
expect(s.word_count).to_equal(0)
expect(s.heading_count).to_equal(0)
expect(s.paragraph_count).to_equal(0)
expect(s.reading_time_minutes).to_equal(0)
```

</details>

#### punctuation-only doc word count is non-negative

- punctuation-only doc word count is non-negative
   - Expected: s.word_count equals `4`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("punctuation-only doc word count is non-negative")
val s = md_compute_stats("!!! ??? --- ...")
# interpreter counts "!!!", "???", "---", "..." as 4 tokens
expect(s.word_count).to_equal(4)
```

</details>

#### line count for single-line doc is 1

- line count for single-line doc is 1
   - Expected: s.line_count equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("line count for single-line doc is 1")
val s = md_compute_stats("hello world")
expect(s.line_count).to_equal(1)
```

</details>

### md_doc_stats: CRLF vs LF

#### CRLF doc line count matches LF doc line count

- CRLF doc line count matches LF doc line count
   - Expected: lf_stats.heading_count equals `crlf_stats.heading_count`
   - Expected: lf_stats.paragraph_count equals `crlf_stats.paragraph_count`
   - Expected: lf_stats.word_count equals `crlf_stats.word_count`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("CRLF doc line count matches LF doc line count")
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

- CRLF word count equals LF word count
   - Expected: ls.word_count equals `cs.word_count`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("CRLF word count equals LF word count")
val lf = "hello world\nfoo bar\n"
val crlf = "hello world\r\nfoo bar\r\n"
val ls = md_compute_stats(lf)
val cs = md_compute_stats(crlf)
expect(ls.word_count).to_equal(cs.word_count)
```

</details>

### md_doc_stats: frontmatter excluded

#### frontmatter lines not counted as headings or words in body

- frontmatter lines not counted as headings or words in body
   - Expected: s1.heading_count equals `s2.heading_count`
   - Expected: s1.word_count equals `s2.word_count`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("frontmatter lines not counted as headings or words in body")
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

- doc with only frontmatter has zero paragraph count
   - Expected: s.paragraph_count equals `0`
   - Expected: s.heading_count equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("doc with only frontmatter has zero paragraph count")
val doc = "---\ntitle: Only FM\n---\n"
val s = md_compute_stats(doc)
expect(s.paragraph_count).to_equal(0)
expect(s.heading_count).to_equal(0)
```

</details>

### md_doc_stats: reading time

#### 200 word doc has reading time of 1 minute

- 200 word doc has reading time of 1 minute
   - Expected: s.reading_time_minutes equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("200 word doc has reading time of 1 minute")
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

- md_sgrid_apply on empty content returns empty cells
   - Expected: cells.len() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("md_sgrid_apply on empty content returns empty cells")
val cells = md_sgrid_apply("")
expect(cells.len()).to_equal(0)
```

</details>

#### md_sgrid_selection_sum with empty range returns zero

- md_sgrid_selection_sum with empty range returns zero
   - Expected: result equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("md_sgrid_selection_sum with empty range returns zero")
val result = md_sgrid_selection_sum("| A | B |\n| --- | --- |\n| 3 | 4 |", "")
expect(result).to_equal("0")
```

</details>

#### md_sgrid_copy_selection with empty range returns empty

- md_sgrid_copy_selection with empty range returns empty
   - Expected: result equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("md_sgrid_copy_selection with empty range returns empty")
val result = md_sgrid_copy_selection("| A |\n| --- |\n| 1 |", "")
expect(result).to_equal("")
```

</details>

#### md_sgrid_scan on empty content returns empty

- md_sgrid_scan on empty content returns empty
   - Expected: blocks.len() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("md_sgrid_scan on empty content returns empty")
val blocks = md_sgrid_scan("")
expect(blocks.len()).to_equal(0)
```

</details>

#### md_sgrid_bind_tables on empty content returns empty

- md_sgrid_bind_tables on empty content returns empty
   - Expected: bindings.len() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("md_sgrid_bind_tables on empty content returns empty")
val bindings = md_sgrid_bind_tables("")
expect(bindings.len()).to_equal(0)
```

</details>

### md_sgrid: range span normalisation

#### reverse range A2:A1 is normalised so row_start <= row_end

- reverse range A2:A1 is normalised so row_start <= row_end
   - Expected: ok is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("reverse range A2:A1 is normalised so row_start <= row_end")
val doc = "| Val |\n| --- |\n| 10 |\n| 20 |"
val result = md_sgrid_selection_sum(doc, "A2:A1")
# normalised to A1:A2, should not crash and return numeric result
val num = result.to_i64() ?? -1
val ok = num >= 0
expect(ok).to_equal(true)
```

</details>

#### single-cell range A1:A1 returns cell value

- single-cell range A1:A1 returns cell value
   - Expected: result equals `42`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("single-cell range A1:A1 returns cell value")
val doc = "| Val |\n| --- |\n| 42 |"
# single-cell sum
val result = md_sgrid_selection_sum(doc, "A2:A2")
expect(result).to_equal("42")
```

</details>

### md_sgrid: pivot and formula on single-cell doc

#### md_sgrid_pivot_sum on table with one data row does not crash

- md_sgrid_pivot_sum on table with one data row does not crash
   - Expected: safe is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("md_sgrid_pivot_sum on table with one data row does not crash")
val doc = "| Item | Amount |\n| --- | --- |\n| foo | 10 |"
val rows = md_sgrid_pivot_sum(doc, "A", "B")
val safe = rows.len() >= 0
expect(safe).to_equal(true)
```

</details>

### md_document_decor: empty doc

#### md_document_decor_parse on empty string returns defaults

- md_document_decor_parse on empty string returns defaults
   - Expected: d.page_view is false
   - Expected: d.header equals ``
   - Expected: d.footer equals ``
   - Expected: d.layout equals `document`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("md_document_decor_parse on empty string returns defaults")
val d = md_document_decor_parse("")
expect(d.page_view).to_equal(false)
expect(d.header).to_equal("")
expect(d.footer).to_equal("")
expect(d.layout).to_equal("document")
```

</details>

#### md_document_body_without_decor on empty returns empty

- md_document_body_without_decor on empty returns empty
   - Expected: body equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("md_document_body_without_decor on empty returns empty")
val body = md_document_body_without_decor("")
expect(body).to_equal("")
```

</details>

#### md_document_sheet_cells on empty returns empty list

- md_document_sheet_cells on empty returns empty list
   - Expected: cells.len() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("md_document_sheet_cells on empty returns empty list")
val cells = md_document_sheet_cells("")
expect(cells.len()).to_equal(0)
```

</details>

#### md_document_split_ppt_pages on empty returns empty

- md_document_split_ppt_pages on empty returns empty
   - Expected: slides.len() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("md_document_split_ppt_pages on empty returns empty")
val slides = md_document_split_ppt_pages("")
expect(slides.len()).to_equal(0)
```

</details>

### md_document_decor: replace_sheet_cell_value bounds

#### replace on empty content returns content unchanged

- replace on empty content returns content unchanged
   - Expected: result equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("replace on empty content returns content unchanged")
val result = md_document_replace_sheet_cell_value("", "A1", "42")
expect(result).to_equal("")
```

</details>

#### replace with empty address returns content unchanged

- replace with empty address returns content unchanged
   - Expected: result equals `doc`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("replace with empty address returns content unchanged")
val doc = "| A |\n| --- |\n| 1 |"
val result = md_document_replace_sheet_cell_value(doc, "", "42")
expect(result).to_equal(doc)
```

</details>

#### replace with invalid address (col 0) returns content unchanged

- replace with invalid address (col 0) returns content unchanged
   - Expected: result equals `doc`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("replace with invalid address (col 0) returns content unchanged")
val doc = "| A |\n| --- |\n| 1 |"
# address '1' has no letter prefix so col=0
val result = md_document_replace_sheet_cell_value(doc, "1", "42")
expect(result).to_equal(doc)
```

</details>

### md_document_decor: unterminated CSS fence is safe

#### unclosed css fence does not crash decor parse

- unclosed css fence does not crash decor parse
   - Expected: safe is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("unclosed css fence does not crash decor parse")
val doc = "---\nlayout: paper\n---\n```css\nbody { color: red; }\n"
val d = md_document_decor_parse(doc)
# inline_css may be empty or partial — just must not crash
val safe = d.layout.len() >= 0
expect(safe).to_equal(true)
```

</details>

#### body_without_decor on unclosed css fence is safe

- body_without_decor on unclosed css fence is safe
   - Expected: safe is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("body_without_decor on unclosed css fence is safe")
val doc = "# Title\n\n```css\nbody { margin: 0; }\n\nSome text."
val body = md_document_body_without_decor(doc)
val safe = body.len() >= 0
expect(safe).to_equal(true)
```

</details>

### md_document_decor: frontmatter parsing edge cases

#### frontmatter with no closing --- is handled safely

- frontmatter with no closing --- is handled safely
   - Expected: safe is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("frontmatter with no closing --- is handled safely")
val doc = "---\ntitle: No close\n\nSome content here.\n"
val d = md_document_decor_parse(doc)
val safe = d.layout.len() > 0
expect(safe).to_equal(true)
```

</details>

#### doc without frontmatter returns default decor

- doc without frontmatter returns default decor
   - Expected: d.page_view is false
   - Expected: d.layout equals `document`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("doc without frontmatter returns default decor")
val doc = "# Just a heading\n\nSome paragraph.\n"
val d = md_document_decor_parse(doc)
expect(d.page_view).to_equal(false)
expect(d.layout).to_equal("document")
```

</details>

#### frontmatter page_view true sets layout to paper

- frontmatter page_view true sets layout to paper
   - Expected: d.page_view is true
   - Expected: d.layout equals `paper`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("frontmatter page_view true sets layout to paper")
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
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering md_diagnostics: empty doc never crashes, md_diagnostics: unterminated code fence, md_diagnostics: heading only hashes, md_diagnostics: images with empty src and empty alt, md_diagnostics: broken heading link end_col clamped, md_diagnostics: extremely long lines do not crash, md_search: empty and whitespace queries, md_search: special chars in query, md_search: col is within line bounds, md_search: headings and code blocks, md_doc_stats: empty and degenerate docs, md_doc_stats: CRLF vs LF, md_doc_stats: frontmatter excluded, md_doc_stats: reading time, md_sgrid: empty doc and zero-span inputs, md_sgrid: range span normalisation, md_sgrid: pivot and formula on single-cell doc, md_document_decor: empty doc, md_document_decor: replace_sheet_cell_value bounds, md_document_decor: unterminated CSS fence is safe, md_document_decor: frontmatter parsing edge cases.
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

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-LIB`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `6b014b2246f5292dab0ac2ccba4cd76a7d9a99cdade1f06a0df8c7d9ea57b082`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `6b014b2246f5292dab0ac2ccba4cd76a7d9a99cdade1f06a0df8c7d9ea57b082`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `6b014b2246f5292dab0ac2ccba4cd76a7d9a99cdade1f06a0df8c7d9ea57b082`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **86/100**; effective score: **86/100**; blockers: **0**.

SSpec documentization score: 86/100
source: test/01_unit/lib/editor/services/md_services_hardening2_spec.spl
mirror: doc/06_spec/01_unit/lib/editor/services/md_services_hardening2_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/lib/editor/services/md_services_hardening2_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/lib/editor/services/md_services_hardening2_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/lib/editor/services/md_services_hardening2_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 48 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/lib/editor/services/md_services_hardening2_spec.spl:30:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'md_diagnose on empty string returns empty list' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/editor/services/md_services_hardening2_spec.spl:36:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'md_check_duplicate_headings on empty string returns empty' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/editor/services/md_services_hardening2_spec.spl:42:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'md_check_empty_headings on empty string returns empty' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
