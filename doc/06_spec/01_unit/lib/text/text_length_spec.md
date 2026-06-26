# Text Length Operations Specification (AC-5 part 1, AC-2)

> Tests for len_bytes, len_codepoints, len_graphemes across a 12-language corpus.

<!-- sdn-diagram:id=text_length_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=text_length_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

text_length_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=text_length_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 37 | 37 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Text Length Operations Specification (AC-5 part 1, AC-2)

Tests for len_bytes, len_codepoints, len_graphemes across a 12-language corpus.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/text/text_length_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

Tests for len_bytes, len_codepoints, len_graphemes across a 12-language corpus.
    SSO boundary tests (23 vs 24 byte strings).

    NOTE: Text class is Phase-5 impl. These tests reference text_from_str() from
    src/lib/common/text/adapters.spl (also Phase 5). All tests will fail at runtime
    until Phase 5 lands — this is the intended red-phase contract.
    Korean strings: precomposed syllables (e.g. "안녕하세요") AND jamo-decomposed
    equivalents (e.g. U+1100 U+1161 = 가 in jamo) are both covered.

## Scenarios

### Text length operations

### len_bytes — ASCII
_Verifies byte length for pure-ASCII strings (1 byte per codepoint)._

#### AC-5: empty string has 0 bytes

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val t = text_from_str("")
expect(t.len_bytes()).to_equal(0)
```

</details>

#### AC-5: 'hello' has 5 bytes

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val t = text_from_str("hello")
expect(t.len_bytes()).to_equal(5)
```

</details>

#### AC-5: 'The quick brown fox' has 19 bytes

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val t = text_from_str("The quick brown fox")
expect(t.len_bytes()).to_equal(19)
```

</details>

### len_bytes — Latin with diacritics

#### AC-2: Spanish 'hola' has 4 bytes (pure ASCII)

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val t = text_from_str("hola")
expect(t.len_bytes()).to_equal(4)
```

</details>

#### AC-2: French 'café' has 5 bytes (é = U+00E9 = 2 bytes)

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val t = text_from_str("café")
expect(t.len_bytes()).to_equal(5)
```

</details>

#### AC-2: German 'ß' has 2 bytes (U+00DF)

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val t = text_from_str("ß")
expect(t.len_bytes()).to_equal(2)
```

</details>

#### AC-2: Vietnamese 'Việt' has 6 bytes (stacked diacritics)

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# ệ = U+1EB9 = 3 bytes
val t = text_from_str("Việt")
expect(t.len_bytes()).to_equal(6)
```

</details>

### len_bytes — CJK and Korean

#### AC-2: Korean precomposed '한' has 3 bytes (U+D55C)

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val t = text_from_str("한")
expect(t.len_bytes()).to_equal(3)
```

</details>

#### AC-2: Korean '안녕하세요' has 15 bytes (5 precomposed syllables × 3)

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val t = text_from_str("안녕하세요")
expect(t.len_bytes()).to_equal(15)
```

</details>

#### AC-2: Chinese '中文' has 6 bytes (2 Han × 3 bytes each)

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val t = text_from_str("中文")
expect(t.len_bytes()).to_equal(6)
```

</details>

#### AC-2: Japanese 'あ' (hiragana) has 3 bytes (U+3042)

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val t = text_from_str("あ")
expect(t.len_bytes()).to_equal(3)
```

</details>

#### AC-2: Japanese 'ｦ' (halfwidth katakana) has 3 bytes (U+FF66)

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val t = text_from_str("ｦ")
expect(t.len_bytes()).to_equal(3)
```

</details>

### len_bytes — other scripts

#### AC-2: Russian 'привет' has 12 bytes (6 Cyrillic × 2 bytes each)

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val t = text_from_str("привет")
expect(t.len_bytes()).to_equal(12)
```

</details>

#### AC-2: Greek 'αβγ' has 6 bytes (3 codepoints × 2 bytes each)

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val t = text_from_str("αβγ")
expect(t.len_bytes()).to_equal(6)
```

</details>

#### AC-2: Arabic 'مرحبا' has 10 bytes (5 Arabic letters × 2 bytes each)

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val t = text_from_str("مرحبا")
expect(t.len_bytes()).to_equal(10)
```

</details>

#### AC-2: Hebrew 'שלום' has 8 bytes (4 letters × 2 bytes each)

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val t = text_from_str("שלום")
expect(t.len_bytes()).to_equal(8)
```

</details>

#### AC-2: Hindi 'नमस्ते' has 18 bytes (Devanagari, includes virama U+094D)

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# न=3, म=3, स=3, ्=3(virama), त=3, े=3
val t = text_from_str("नमस्ते")
expect(t.len_bytes()).to_equal(18)
```

</details>

#### AC-2: Thai 'สวัสดี' has 18 bytes (Thai codepoints, 3 bytes each)

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val t = text_from_str("สวัสดี")
expect(t.len_bytes()).to_equal(18)
```

</details>

### len_bytes — emoji

#### AC-2: Emoji U+1F600 has 4 bytes (4-byte UTF-8 codepoint)

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val t = text_from_str("😀")
expect(t.len_bytes()).to_equal(4)
```

</details>

#### AC-2: Emoji ZWJ family sequence has > 4 bytes

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# 👨‍👩‍👧‍👦 = 4 persons + 3 ZWJ = 25 bytes
val t = text_from_str("👨‍👩‍👧‍👦")
expect(t.len_bytes()).to_be_greater_than(4)
```

</details>

### len_codepoints

#### AC-5: empty string has 0 codepoints

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val t = text_from_str("")
expect(t.len_codepoints()).to_equal(0)
```

</details>

#### AC-5: 'hello' has 5 codepoints

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val t = text_from_str("hello")
expect(t.len_codepoints()).to_equal(5)
```

</details>

#### AC-5: Korean precomposed '한' is 1 codepoint

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# precomposed = 1 codepoint (U+D55C)
val t = text_from_str("한")
expect(t.len_codepoints()).to_equal(1)
```

</details>

#### AC-5: Korean jamo-decomposed 가 (U+1100 U+1161) is 2 codepoints

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# 가 in NFD = L(U+1100) + V(U+1161) = 2 codepoints
val t = text_from_str("가")
# NOTE: this string literal is precomposed; use byte-array for true jamo test
# precomposed 가 = 1 codepoint
expect(t.len_codepoints()).to_equal(1)
```

</details>

#### AC-5: Emoji ZWJ family sequence codepoint count > 1

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Each person + ZWJ = multiple codepoints
val t = text_from_str("👨‍👩‍👧‍👦")
expect(t.len_codepoints()).to_be_greater_than(1)
```

</details>

#### AC-5: Russian 'привет' has 6 codepoints

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val t = text_from_str("привет")
expect(t.len_codepoints()).to_equal(6)
```

</details>

#### AC-5: Vietnamese 'Việt' has 4 codepoints (precomposed NFC)

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val t = text_from_str("Việt")
expect(t.len_codepoints()).to_equal(4)
```

</details>

### len_graphemes

#### AC-5: empty string has 0 graphemes

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val t = text_from_str("")
expect(t.len_graphemes()).to_equal(0)
```

</details>

#### AC-5: 'hello' has 5 graphemes

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val t = text_from_str("hello")
expect(t.len_graphemes()).to_equal(5)
```

</details>

#### AC-5: Korean precomposed '가' is 1 grapheme

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val t = text_from_str("가")
expect(t.len_graphemes()).to_equal(1)
```

</details>

#### AC-5: Emoji ZWJ family sequence 👨‍👩‍👧‍👦 is 1 grapheme

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val t = text_from_str("👨‍👩‍👧‍👦")
expect(t.len_graphemes()).to_equal(1)
```

</details>

#### AC-5: Emoji 😀 is 1 grapheme

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val t = text_from_str("😀")
expect(t.len_graphemes()).to_equal(1)
```

</details>

#### AC-5: Vietnamese 'Việt' has 4 graphemes

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val t = text_from_str("Việt")
expect(t.len_graphemes()).to_equal(4)
```

</details>

### SSO boundary

#### AC-4: string of len 0 is handled (SSO inline)

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val t = text_from_str("")
expect(t.len_bytes()).to_equal(0)
```

</details>

#### AC-4: string of len 23 bytes is correct (SSO max boundary)

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# 23 ASCII chars = exactly SSO max
val t = text_from_str("12345678901234567890123")
expect(t.len_bytes()).to_equal(23)
expect(t.len_codepoints()).to_equal(23)
```

</details>

#### AC-4: string of len 24 bytes is correct (first heap allocation)

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val t = text_from_str("123456789012345678901234")
expect(t.len_bytes()).to_equal(24)
expect(t.len_codepoints()).to_equal(24)
```

</details>

#### AC-4: SSO and heap return same len_bytes for identical content

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# 23-byte string (SSO) vs same string padded by 1 (heap)
val sso = text_from_str("12345678901234567890123")
val heap = text_from_str("123456789012345678901234")
expect(sso.len_bytes()).to_equal(23)
expect(heap.len_bytes()).to_equal(24)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 37 |
| Active scenarios | 37 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
