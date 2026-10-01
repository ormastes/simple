# Simple Web Html Layout Renderer Scan Index Space Specification

> Tests covering web renderer scanners are byte-indexed end to end, text_matches_at probes byte offsets, skip_wrap_spaces returns byte offsets, the HTML admission guard scans in byte index space.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 20 | 20 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Simple Web Html Layout Renderer Scan Index Space Specification

## Scenarios

### web renderer scanners are byte-indexed end to end

#### agrees with byte-indexed index_of on pure ASCII (control)

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- agrees with byte-indexed index_of on pure ASCII (control)


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("agrees with byte-indexed index_of on pure ASCII (control)")
expect(find_from("abcZdef", "Z", 0)).to_be("abcZdef".index_of("Z"))
expect(find_from("abcZdef", "Z", 0)).to_be(3)
```

</details>

#### agrees with index_of across a 2-byte UTF-8 sequence

- agrees with index_of across a 2-byte UTF-8 sequence


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("agrees with index_of across a 2-byte UTF-8 sequence")
# "caf<U+00E9>Zdef" -> 9 bytes, 8 characters. 'Z' is byte 5, char 4.
val doc = "caféZdef"
expect(doc.len()).to_be(9)
expect(find_from(doc, "Z", 0)).to_be(doc.index_of("Z"))
expect(find_from(doc, "Z", 0)).to_be(5)
```

</details>

#### agrees with index_of across a 3-byte UTF-8 sequence

- agrees with index_of across a 3-byte UTF-8 sequence


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("agrees with index_of across a 3-byte UTF-8 sequence")
val doc = "a世界Zdef"
expect(find_from(doc, "Z", 0)).to_be(doc.index_of("Z"))
expect(find_from(doc, "Z", 0)).to_be(7)
```

</details>

#### agrees with index_of across a 4-byte UTF-8 sequence

- agrees with index_of across a 4-byte UTF-8 sequence


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("agrees with index_of across a 4-byte UTF-8 sequence")
val doc = "a😀Zdef"
expect(find_from(doc, "Z", 0)).to_be(doc.index_of("Z"))
expect(find_from(doc, "Z", 0)).to_be(5)
```

</details>

#### returns an offset that indexes the byte array, not the character array

- returns an offset that indexes the byte array, not the character array


<details>
<summary>Executable SSpec</summary>

Runnable source: 17 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns an offset that indexes the byte array, not the character array")
# The load-bearing property: the returned index is a BYTE index, so it
# addresses the same position `len()`/`index_of()` speak in. Asserted
# against `bytes()` rather than `substring()` on purpose -- see the
# engine-divergence note at the bottom of this file: the interpreter's
# `substring`/`slice` are CHARACTER-indexed while its `len`/`index_of`
# are byte-indexed, so a substring round-trip here would be testing that
# builtin bug rather than these scanners.
val doc = "caféZdef"
val at = find_from(doc, "Z", 0)
val b = doc.bytes()
expect(at).to_be(5)
expect(b[at]).to_be(90)        # 'Z'
expect(b[at + 1]).to_be(100)   # 'd'
expect(b[at + 2]).to_be(101)   # 'e'
expect(b[at + 3]).to_be(102)   # 'f'
```

</details>

#### finds a needle occurring after a multi-byte character in real CSS

- finds a needle occurring after a multi-byte character in real CSS


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("finds a needle occurring after a multi-byte character in real CSS")
val css = "/* café */ .a { color: red }"
val at = find_from(css, "color", 0)
val b = css.bytes()
expect(at).to_be(css.index_of("color"))
expect(b[at]).to_be(99)        # 'c'
expect(b[at + 1]).to_be(111)   # 'o'
expect(b[at + 2]).to_be(108)   # 'l'
expect(b[at + 3]).to_be(111)   # 'o'
expect(b[at + 4]).to_be(114)   # 'r'
```

</details>

#### locates a multi-byte needle itself

- locates a multi-byte needle itself


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("locates a multi-byte needle itself")
val doc = "abc界def"
val at = find_from(doc, "界", 0)
val b = doc.bytes()
expect(at).to_be(doc.index_of("界"))
expect(at).to_be(3)
# U+754C encodes as E7 95 8C
expect(b[at]).to_be(231)
expect(b[at + 1]).to_be(149)
expect(b[at + 2]).to_be(140)
```

</details>

#### resumes correctly from a byte offset past a multi-byte character

- resumes correctly from a byte offset past a multi-byte character


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("resumes correctly from a byte offset past a multi-byte character")
# Second 'Z' only: start scanning after the first one.
val doc = "a世Zb世Z"
val first = find_from(doc, "Z", 0)
val second = find_from(doc, "Z", first + 1)
expect(first).to_be(4)
expect(second).to_be(9)
expect(doc.bytes()[second]).to_be(90)
```

</details>

#### handles empty strings, index 0, last index and out-of-range

- handles empty strings, index 0, last index and out-of-range


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("handles empty strings, index 0, last index and out-of-range")
expect(find_from("", "Z", 0)).to_be(-1)
expect(find_from("Zabc", "Z", 0)).to_be(0)
expect(find_from("abcZ", "Z", 0)).to_be(3)
expect(find_from("abc", "Z", 0)).to_be(-1)
expect(find_from("abc", "", 0)).to_be(0)
expect(find_from("abc", "b", 99)).to_be(-1)
expect(find_from("abc", "b", -5)).to_be(1)
```

</details>

#### text_index_of matches native byte-indexed index_of on multi-byte input

- text_index_of matches native byte-indexed index_of on multi-byte input


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("text_index_of matches native byte-indexed index_of on multi-byte input")
val doc = "héllo wörld"
expect(text_index_of(doc, "wörld")).to_be(doc.index_of("wörld"))
expect(text_index_of(doc, "llo")).to_be(doc.index_of("llo"))
```

</details>

### text_matches_at probes byte offsets

#### matches at a byte offset that lands on a multi-byte character

- matches at a byte offset that lands on a multi-byte character


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("matches at a byte offset that lands on a multi-byte character")
# byte 3 is the first byte of <U+00E9>; a 2-byte needle must match there.
expect(text_matches_at("café", "é", 3)).to_be(true)
```

</details>

#### matches an ASCII needle sitting after a multi-byte character

- matches an ASCII needle sitting after a multi-byte character


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("matches an ASCII needle sitting after a multi-byte character")
val doc = "caféZdef"
expect(text_matches_at(doc, "Zdef", 5)).to_be(true)
# char-index 4 is where the buggy scanner looked; it is NOT a match.
expect(text_matches_at(doc, "Zdef", 4)).to_be(false)
```

</details>

#### rejects negative and out-of-range offsets

- rejects negative and out-of-range offsets


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rejects negative and out-of-range offsets")
expect(text_matches_at("abc", "c", -1)).to_be(false)
expect(text_matches_at("abc", "c", 99)).to_be(false)
expect(text_matches_at("abc", "abcd", 0)).to_be(false)
```

</details>

#### matches at index 0 and at the last index

- matches at index 0 and at the last index


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("matches at index 0 and at the last index")
expect(text_matches_at("abc", "a", 0)).to_be(true)
expect(text_matches_at("abc", "c", 2)).to_be(true)
```

</details>

### skip_wrap_spaces returns byte offsets

#### returns a byte offset after skipping spaces following multi-byte text

- returns a byte offset after skipping spaces following multi-byte text


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns a byte offset after skipping spaces following multi-byte text")
# "世界   Z" -> 世界 is 6 bytes, then 3 spaces, then Z at byte 9.
val doc = "世界   Z"
expect(doc.len()).to_be(10)
expect(skip_wrap_spaces(doc, 6)).to_be(9)
expect(doc.bytes()[skip_wrap_spaces(doc, 6)]).to_be(90)   # 'Z'
```

</details>

#### is a no-op when the offset is already non-space

- is a no-op when the offset is already non-space


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("is a no-op when the offset is already non-space")
expect(skip_wrap_spaces("abc", 0)).to_be(0)
expect(skip_wrap_spaces("  abc", 0)).to_be(2)
```

</details>

### the HTML admission guard scans in byte index space

#### proves len() is bytes while char_code_at is characters

- proves len() is bytes while char_code_at is characters


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("proves len() is bytes while char_code_at is characters")
# The mismatch the guard used to have, stated as an executable fact:
# 6 bytes, 5 characters, so a len()-bounded character scan runs one
# index past the end and reads a character that does not exist.
val doc = "café,"
expect(doc.len()).to_be(6)
expect(doc.char_code_at(3)).to_be(233)     # 'é' as a CODEPOINT
expect(doc.byte_at(3)).to_be(195)          # 0xC3 lead byte at the same index
expect(doc.char_code_at(5)).to_be(0)       # phantom: the over-run tail
expect(doc.byte_at(5)).to_be(44)           # the real last byte, ','
```

</details>

#### admits an ASCII document (control)

- admits an ASCII document (control)


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("admits an ASCII document (control)")
assert_true(_simple_web_html_source_admitted("<html><body>hi</body></html>", SIMPLE_WEB_MAX_HTML_BYTES))
```

</details>

#### admits a multi-byte document without over-running its index space

- admits a multi-byte document without over-running its index space


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("admits a multi-byte document without over-running its index space")
assert_true(_simple_web_html_source_admitted("<p>café — naïve 中文</p>", SIMPLE_WEB_MAX_HTML_BYTES))
```

</details>

#### still rejects a payload over the byte limit

- still rejects a payload over the byte limit


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("still rejects a payload over the byte limit")
# The limit is a BYTE limit and is compared against `len()`, so a
# multi-byte document is measured in bytes, not characters.
val doc = "<p>café</p>"
expect(doc.len()).to_be(12)
assert_false(_simple_web_html_source_admitted(doc, 11))
assert_true(_simple_web_html_source_admitted(doc, 12))
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/gc_async_mut/gpu/browser_engine/simple_web_html_layout_renderer_scan_index_space_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering web renderer scanners are byte-indexed end to end, text_matches_at probes byte offsets, skip_wrap_spaces returns byte offsets, the HTML admission guard scans in byte index space.
- web renderer scanners are byte-indexed end to end
- text_matches_at probes byte offsets
- skip_wrap_spaces returns byte offsets
- the HTML admission guard scans in byte index space

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 20 |
| Active scenarios | 20 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-UNIT`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `bbabb4e4274f8f43fefc82045b41225d78692b6c65b27a29d8b93d7810913337`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `bbabb4e4274f8f43fefc82045b41225d78692b6c65b27a29d8b93d7810913337`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `bbabb4e4274f8f43fefc82045b41225d78692b6c65b27a29d8b93d7810913337`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/01_unit/lib/gc_async_mut/gpu/browser_engine/simple_web_html_layout_renderer_scan_index_space_spec.spl
mirror: doc/06_spec/01_unit/lib/gc_async_mut/gpu/browser_engine/simple_web_html_layout_renderer_scan_index_space_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/lib/gc_async_mut/gpu/browser_engine/simple_web_html_layout_renderer_scan_index_space_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/lib/gc_async_mut/gpu/browser_engine/simple_web_html_layout_renderer_scan_index_space_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/lib/gc_async_mut/gpu/browser_engine/simple_web_html_layout_renderer_scan_index_space_spec.spl:30:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'agrees with byte-indexed index_of on pure ASCII (control)' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/gc_async_mut/gpu/browser_engine/simple_web_html_layout_renderer_scan_index_space_spec.spl:36:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'agrees with index_of across a 2-byte UTF-8 sequence' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/gc_async_mut/gpu/browser_engine/simple_web_html_layout_renderer_scan_index_space_spec.spl:45:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'agrees with index_of across a 3-byte UTF-8 sequence' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
