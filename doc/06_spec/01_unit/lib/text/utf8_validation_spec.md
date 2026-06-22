# UTF-8 Validation Specification (AC-1)

> Tests for UTF-8 byte sequence validation, encoding/decoding invariants,

<!-- sdn-diagram:id=utf8_validation_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=utf8_validation_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

utf8_validation_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=utf8_validation_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 26 | 26 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# UTF-8 Validation Specification (AC-1)

Tests for UTF-8 byte sequence validation, encoding/decoding invariants,

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/text/utf8_validation_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

Tests for UTF-8 byte sequence validation, encoding/decoding invariants,
    overlong sequences, lone surrogates, and out-of-range codepoints.

    NOTE: trait header conformance `class X: Encoding` fails to parse (2026-04-26 bug).
    These tests use top-level function calls (utf8_is_valid, utf8_encode_one, etc.)
    rather than trait-dispatch. Phase 5 will wire SIMD path; Phase 7 will verify parity.

## Scenarios

### UTF-8 Validation

### valid sequences — 1-byte (ASCII)
_Verifies single-byte ASCII codepoints (U+0000..U+007F) validate correctly._

#### AC-1: single ASCII byte 0x41 ('A') is valid

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val bytes: [i64] = [65]
expect(utf8_is_valid(bytes)).to_equal(true)
```

</details>

#### AC-1: NUL byte 0x00 is valid UTF-8

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val bytes: [i64] = [0]
expect(utf8_is_valid(bytes)).to_equal(true)
```

</details>

#### AC-1: DEL byte 0x7F is valid UTF-8 (max 1-byte)

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val bytes: [i64] = [127]
expect(utf8_is_valid(bytes)).to_equal(true)
```

</details>

### valid sequences — 2-byte

#### AC-1: U+00E9 (é) encodes to 2 bytes 0xC3 0xA9

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val cp: i64 = 0xE9
val encoded = utf8_encode_one(cp)
expect(encoded.len()).to_equal(2)
expect(utf8_is_valid(encoded)).to_equal(true)
```

</details>

#### AC-1: U+0080 (minimum 2-byte) is valid

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val bytes: [i64] = [0xC2, 0x80]
expect(utf8_is_valid(bytes)).to_equal(true)
```

</details>

#### AC-1: U+07FF (maximum 2-byte) is valid

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val bytes: [i64] = [0xDF, 0xBF]
expect(utf8_is_valid(bytes)).to_equal(true)
```

</details>

### valid sequences — 3-byte

#### AC-1: U+D55C (한) encodes to 3 bytes

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val cp: i64 = 0xD55C
val encoded = utf8_encode_one(cp)
expect(encoded.len()).to_equal(3)
expect(utf8_is_valid(encoded)).to_equal(true)
```

</details>

#### AC-1: U+AC00 (가, Hangul syllable base) is valid

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val cp: i64 = 0xAC00
val encoded = utf8_encode_one(cp)
expect(encoded.len()).to_equal(3)
expect(utf8_is_valid(encoded)).to_equal(true)
```

</details>

#### AC-1: U+4E2D (中) encodes to 3 bytes

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val cp: i64 = 0x4E2D
val encoded = utf8_encode_one(cp)
expect(encoded.len()).to_equal(3)
expect(utf8_is_valid(encoded)).to_equal(true)
```

</details>

### valid sequences — 4-byte

#### AC-1: U+1F600 (emoji) encodes to 4 bytes

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val cp: i64 = 0x1F600
val encoded = utf8_encode_one(cp)
expect(encoded.len()).to_equal(4)
expect(utf8_is_valid(encoded)).to_equal(true)
```

</details>

#### AC-1: U+10000 (minimum 4-byte) is valid

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val bytes: [i64] = [0xF0, 0x90, 0x80, 0x80]
expect(utf8_is_valid(bytes)).to_equal(true)
```

</details>

#### AC-1: U+10FFFF (maximum valid codepoint) is valid

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val bytes: [i64] = [0xF4, 0x8F, 0xBF, 0xBF]
expect(utf8_is_valid(bytes)).to_equal(true)
```

</details>

### invalid: overlong sequences

#### AC-1: overlong NUL (0xC0 0x80) is invalid

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val bytes: [i64] = [0xC0, 0x80]
expect(utf8_is_valid(bytes)).to_equal(false)
```

</details>

#### AC-1: overlong 0xE0 0x80 0x80 is invalid

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val bytes: [i64] = [0xE0, 0x80, 0x80]
expect(utf8_is_valid(bytes)).to_equal(false)
```

</details>

#### AC-1: overlong 0xF0 0x80 0x80 0x80 is invalid

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val bytes: [i64] = [0xF0, 0x80, 0x80, 0x80]
expect(utf8_is_valid(bytes)).to_equal(false)
```

</details>

### invalid: lone surrogates

#### AC-1: U+D800 (low surrogate as 3-byte UTF-8) is invalid

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# 0xED 0xA0 0x80 encodes U+D800 — lone surrogate
val bytes: [i64] = [0xED, 0xA0, 0x80]
expect(utf8_is_valid(bytes)).to_equal(false)
```

</details>

#### AC-1: U+DFFF (high surrogate as 3-byte UTF-8) is invalid

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# 0xED 0xBF 0xBF encodes U+DFFF
val bytes: [i64] = [0xED, 0xBF, 0xBF]
expect(utf8_is_valid(bytes)).to_equal(false)
```

</details>

### invalid: codepoints beyond U+10FFFF

#### AC-1: 0xF4 0x90 0x80 0x80 (U+110000) is invalid

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val bytes: [i64] = [0xF4, 0x90, 0x80, 0x80]
expect(utf8_is_valid(bytes)).to_equal(false)
```

</details>

### invalid: truncated sequences

#### AC-1: lone continuation byte 0x80 is invalid

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val bytes: [i64] = [0x80]
expect(utf8_is_valid(bytes)).to_equal(false)
```

</details>

#### AC-1: 2-byte lead with no continuation is invalid

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val bytes: [i64] = [0xC3]
expect(utf8_is_valid(bytes)).to_equal(false)
```

</details>

### BOM handling

#### AC-1: UTF-8 BOM sequence 0xEF 0xBB 0xBF is valid UTF-8 bytes

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# BOM is codepoint U+FEFF encoded as 3 bytes — valid UTF-8
val bytes: [i64] = [0xEF, 0xBB, 0xBF]
expect(utf8_is_valid(bytes)).to_equal(true)
```

</details>

### round-trip encode/decode

#### AC-1: encode then decode U+D55C (한) returns same codepoint

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val cp: i64 = 0xD55C
val encoded = utf8_encode_one(cp)
val decoded = utf8_decode_one(encoded, 0)
expect(decoded[0]).to_equal(cp)
```

</details>

#### AC-1: encode then decode U+1F600 (emoji) returns same codepoint

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val cp: i64 = 0x1F600
val encoded = utf8_encode_one(cp)
val decoded = utf8_decode_one(encoded, 0)
expect(decoded[0]).to_equal(cp)
```

</details>

#### AC-1: text_codepoint_len matches utf8_count_codepoints for ASCII

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val s = "hello"
expect(text_codepoint_len(s)).to_equal(5)
```

</details>

#### AC-1: text_byte_len returns 3 for single Hangul syllable 한

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val s = "한"
expect(text_byte_len(s)).to_equal(3)
```

</details>

#### AC-1: text_codepoint_len returns 1 for single Hangul syllable 한

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val s = "한"
expect(text_codepoint_len(s)).to_equal(1)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 26 |
| Active scenarios | 26 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
