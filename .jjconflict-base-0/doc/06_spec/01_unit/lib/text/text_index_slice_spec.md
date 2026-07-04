# Text Index and Slice Specification (AC-5 part 2)

> Tests for cp_at(i) and slice_codepoints(s, e) across mixed-width corpus.

<!-- sdn-diagram:id=text_index_slice_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=text_index_slice_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

text_index_slice_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=text_index_slice_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 17 | 17 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Text Index and Slice Specification (AC-5 part 2)

Tests for cp_at(i) and slice_codepoints(s, e) across mixed-width corpus.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/text/text_index_slice_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

Tests for cp_at(i) and slice_codepoints(s, e) across mixed-width corpus.

    NOTE: Text class and TextView are Phase-5 impl. All tests reference
    src/lib/common/text/text.spl and text_view.spl (not yet created).
    Tests will fail at runtime until Phase 5 lands — red-phase contract.

## Scenarios

### Text index and slice operations

### cp_at — ASCII
_Verifies cp_at returns correct codepoints for ASCII characters._

#### AC-5: cp_at(0) on 'hello' returns codepoint for 'h' (104)

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val t = text_from_str("hello")
expect(t.cp_at(0)).to_equal(104)
```

</details>

#### AC-5: cp_at(4) on 'hello' returns codepoint for 'o' (111)

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val t = text_from_str("hello")
expect(t.cp_at(4)).to_equal(111)
```

</details>

### cp_at — mixed-width Korean + ASCII

#### AC-5: cp_at(0) on '한a' returns codepoint U+D55C (54620)

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val t = text_from_str("한a")
expect(t.cp_at(0)).to_equal(0xD55C)
```

</details>

#### AC-5: cp_at(1) on '한a' returns codepoint for 'a' (97)

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val t = text_from_str("한a")
expect(t.cp_at(1)).to_equal(97)
```

</details>

#### AC-5: cp_at(0) on '가' (AC00, Hangul syllable base) returns 0xAC00

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val t = text_from_str("가")
expect(t.cp_at(0)).to_equal(0xAC00)
```

</details>

### cp_at — 4-byte codepoints

#### AC-5: cp_at(0) on emoji '😀' returns U+1F600 (128512)

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val t = text_from_str("😀")
expect(t.cp_at(0)).to_equal(0x1F600)
```

</details>

#### AC-5: cp_at(1) on 'a😀b' returns U+1F600

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val t = text_from_str("a😀b")
expect(t.cp_at(1)).to_equal(0x1F600)
```

</details>

#### AC-5: cp_at(2) on 'a😀b' returns codepoint for 'b' (98)

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val t = text_from_str("a😀b")
expect(t.cp_at(2)).to_equal(98)
```

</details>

### slice_codepoints — boundary cases

#### AC-5: empty slice (s==e) returns empty TextView

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val t = text_from_str("hello")
val view = t.slice_codepoints(2, 2)
expect(view.len_bytes()).to_equal(0)
```

</details>

#### AC-5: full slice returns all bytes

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val t = text_from_str("hello")
val view = t.slice_codepoints(0, 5)
expect(view.len_bytes()).to_equal(5)
```

</details>

#### AC-5: middle slice 'ell' from 'hello' has 3 bytes

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val t = text_from_str("hello")
val view = t.slice_codepoints(1, 4)
expect(view.len_bytes()).to_equal(3)
```

</details>

### slice_codepoints — mixed-width Korean

#### AC-5: slice 1 Korean codepoint from '안녕' returns 3 bytes

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val t = text_from_str("안녕")
val view = t.slice_codepoints(0, 1)
# 안 = U+C548 = 3 bytes
expect(view.len_bytes()).to_equal(3)
```

</details>

#### AC-5: slice both Korean codepoints from '안녕' returns 6 bytes

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val t = text_from_str("안녕")
val view = t.slice_codepoints(0, 2)
expect(view.len_bytes()).to_equal(6)
```

</details>

#### AC-5: slice Hangul syllable 가 (AC00) from mixed string returns 3 bytes

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val t = text_from_str("a가b")
val view = t.slice_codepoints(1, 2)
expect(view.len_bytes()).to_equal(3)
```

</details>

### slice_codepoints — 4-byte emoji

#### AC-5: slice emoji U+1F600 from 'a😀b' returns 4 bytes

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val t = text_from_str("a😀b")
val view = t.slice_codepoints(1, 2)
expect(view.len_bytes()).to_equal(4)
```

</details>

### slice_codepoints — out-of-bounds saturation

#### AC-5: slice with e > len saturates to len (no panic)

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val t = text_from_str("hi")
val view = t.slice_codepoints(0, 100)
# Should return entire string, not panic
expect(view.len_bytes()).to_equal(2)
```

</details>

#### AC-5: slice with s > len returns empty (no panic)

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val t = text_from_str("hi")
val view = t.slice_codepoints(100, 200)
expect(view.len_bytes()).to_equal(0)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 17 |
| Active scenarios | 17 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
