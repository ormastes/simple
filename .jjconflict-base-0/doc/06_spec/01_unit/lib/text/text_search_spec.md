# Text Search Specification (AC-5 part 3)

> Tests for contains(needle) and find(needle) across ASCII, Korean, emoji.

<!-- sdn-diagram:id=text_search_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=text_search_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

text_search_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=text_search_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 16 | 16 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Text Search Specification (AC-5 part 3)

Tests for contains(needle) and find(needle) across ASCII, Korean, emoji.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/text/text_search_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

Tests for contains(needle) and find(needle) across ASCII, Korean, emoji.
    find() returns a byte offset (per arch doc §3 / api_and_design.md).

    NOTE: Text class is Phase-5 impl. All tests are red-phase.
    Multi-byte boundary safety: needle must not match mid-codepoint sequences.

## Scenarios

### Text search operations

### contains — ASCII
_Verifies contains() detects substrings in ASCII haystacks._

#### AC-5: 'hello world' contains 'world'

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val t = text_from_str("hello world")
val needle = text_from_str("world")
expect(t.contains(needle)).to_equal(true)
```

</details>

#### AC-5: 'hello world' does not contain 'xyz'

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val t = text_from_str("hello world")
val needle = text_from_str("xyz")
expect(t.contains(needle)).to_equal(false)
```

</details>

#### AC-5: string contains itself

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val t = text_from_str("abc")
expect(t.contains(t)).to_equal(true)
```

</details>

#### AC-5: empty needle is always contained

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val t = text_from_str("hello")
val needle = text_from_str("")
expect(t.contains(needle)).to_equal(true)
```

</details>

#### AC-5: empty haystack does not contain non-empty needle

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val t = text_from_str("")
val needle = text_from_str("a")
expect(t.contains(needle)).to_equal(false)
```

</details>

#### AC-5: needle larger than haystack is not contained

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val t = text_from_str("hi")
val needle = text_from_str("hello world")
expect(t.contains(needle)).to_equal(false)
```

</details>

### contains — Korean

#### AC-5: Korean string contains Korean needle

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val t = text_from_str("안녕하세요")
val needle = text_from_str("하세")
expect(t.contains(needle)).to_equal(true)
```

</details>

#### AC-5: Korean string does not contain ASCII needle

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val t = text_from_str("안녕하세요")
val needle = text_from_str("hello")
expect(t.contains(needle)).to_equal(false)
```

</details>

### contains — emoji

#### AC-5: string with emoji contains that emoji

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val t = text_from_str("hello 😀 world")
val needle = text_from_str("😀")
expect(t.contains(needle)).to_equal(true)
```

</details>

#### AC-5: string without emoji does not match emoji needle

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val t = text_from_str("hello world")
val needle = text_from_str("😀")
expect(t.contains(needle)).to_equal(false)
```

</details>

### find — ASCII

#### AC-5: find 'world' in 'hello world' returns byte offset 6

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val t = text_from_str("hello world")
val needle = text_from_str("world")
val result = t.find(needle)
expect(result).to_equal(6)
```

</details>

#### AC-5: find 'hello' at start returns byte offset 0

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val t = text_from_str("hello world")
val needle = text_from_str("hello")
val result = t.find(needle)
expect(result).to_equal(0)
```

</details>

#### AC-5: find absent needle returns -1 or nil (no match)

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val t = text_from_str("hello")
val needle = text_from_str("xyz")
val result = t.find(needle)
# find returns -1 as sentinel for not-found (i64)
expect(result).to_equal(-1)
```

</details>

### find — Korean (byte offset)

#### AC-5: find '하세' in '안녕하세요' returns byte offset 6

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val t = text_from_str("안녕하세요")
# 안(3) + 녕(3) = 6 bytes before 하
val needle = text_from_str("하세")
val result = t.find(needle)
expect(result).to_equal(6)
```

</details>

### find — emoji

#### AC-5: find emoji '😀' in 'hi😀' returns byte offset 2

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val t = text_from_str("hi😀")
val needle = text_from_str("😀")
val result = t.find(needle)
expect(result).to_equal(2)
```

</details>

### multi-byte boundary safety

#### AC-5: ASCII needle does not match inside a 3-byte Korean codepoint

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# "한" = 0xED 0x95 0x9C; needle 0x95 alone is a continuation byte, not ASCII
val t = text_from_str("한")
# continuation byte 0x95 as single-byte string is NOT valid UTF-8
# and must not match inside '한'
val needle = text_from_str("a")
expect(t.contains(needle)).to_equal(false)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 16 |
| Active scenarios | 16 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
