# utf8_spec

> Purpose: Prove that utf8_seq_len.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 58 | 58 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# utf8_spec

Purpose: Prove that utf8_seq_len.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/common/encoding/utf8_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Purpose and audience
Purpose: Prove that utf8_seq_len.
Audience: compiler and tooling engineers who maintain this spec.

## Scenarios

### utf8_seq_len

#### returns 1 for ASCII bytes

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- returns 1 for ASCII bytes
- Verify: returns 1 for ASCII bytes
   - Expected: utf8_seq_len(0x00) equals `1`
   - Expected: utf8_seq_len(0x41) equals `1`
   - Expected: utf8_seq_len(0x7F) equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("returns 1 for ASCII bytes")
step("Verify: returns 1 for ASCII bytes")
# @req: REQ-LIB-COMMON-001
expect(utf8_seq_len(0x00)).to_equal(1)  # oracle: 1 — named expected value from the requirement
expect(utf8_seq_len(0x41)).to_equal(1)  # oracle: 1 — named expected value from the requirement
expect(utf8_seq_len(0x7F)).to_equal(1)  # oracle: 1 — named expected value from the requirement
```

</details>

#### returns 0 for continuation bytes

- returns 0 for continuation bytes
- Verify: returns 0 for continuation bytes
   - Expected: utf8_seq_len(0x80) equals `0`
   - Expected: utf8_seq_len(0xBF) equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("returns 0 for continuation bytes")
step("Verify: returns 0 for continuation bytes")
expect(utf8_seq_len(0x80)).to_equal(0)  # oracle: 0 — named expected value from the requirement
expect(utf8_seq_len(0xBF)).to_equal(0)  # oracle: 0 — named expected value from the requirement
```

</details>

#### returns 2 for 2-byte lead

- returns 2 for 2-byte lead
- Verify: returns 2 for 2-byte lead
   - Expected: utf8_seq_len(0xC0) equals `2`
   - Expected: utf8_seq_len(0xDF) equals `2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("returns 2 for 2-byte lead")
step("Verify: returns 2 for 2-byte lead")
expect(utf8_seq_len(0xC0)).to_equal(2)  # oracle: 2 — named expected value from the requirement
expect(utf8_seq_len(0xDF)).to_equal(2)  # oracle: 2 — named expected value from the requirement
```

</details>

#### returns 3 for 3-byte lead

- returns 3 for 3-byte lead
- Verify: returns 3 for 3-byte lead
   - Expected: utf8_seq_len(0xE0) equals `3`
   - Expected: utf8_seq_len(0xEF) equals `3`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("returns 3 for 3-byte lead")
step("Verify: returns 3 for 3-byte lead")
expect(utf8_seq_len(0xE0)).to_equal(3)  # oracle: 3 — named expected value from the requirement
expect(utf8_seq_len(0xEF)).to_equal(3)  # oracle: 3 — named expected value from the requirement
```

</details>

#### returns 4 for 4-byte lead

- returns 4 for 4-byte lead
- Verify: returns 4 for 4-byte lead
   - Expected: utf8_seq_len(0xF0) equals `4`
   - Expected: utf8_seq_len(0xF7) equals `4`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("returns 4 for 4-byte lead")
step("Verify: returns 4 for 4-byte lead")
expect(utf8_seq_len(0xF0)).to_equal(4)  # oracle: 4 — named expected value from the requirement
expect(utf8_seq_len(0xF7)).to_equal(4)  # oracle: 4 — named expected value from the requirement
```

</details>

#### returns 0 for invalid lead bytes

- returns 0 for invalid lead bytes
- Verify: returns 0 for invalid lead bytes
   - Expected: utf8_seq_len(0xF8) equals `0`
   - Expected: utf8_seq_len(0xFF) equals `0`
   - Expected: utf8_seq_len(-1) equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("returns 0 for invalid lead bytes")
step("Verify: returns 0 for invalid lead bytes")
expect(utf8_seq_len(0xF8)).to_equal(0)  # oracle: 0 — named expected value from the requirement
expect(utf8_seq_len(0xFF)).to_equal(0)  # oracle: 0 — named expected value from the requirement
expect(utf8_seq_len(-1)).to_equal(0)  # oracle: 0 — named expected value from the requirement
```

</details>

### utf8_encode_one

#### encodes ASCII codepoints as single byte

- encodes ASCII codepoints as single byte
- Verify: encodes ASCII codepoints as single byte
   - Expected: utf8_encode_one(0x41) equals `[0x41])  # 'A'`
   - Expected: utf8_encode_one(0x00) equals `[0x00]`
   - Expected: utf8_encode_one(0x7F) equals `[0x7F]`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("encodes ASCII codepoints as single byte")
step("Verify: encodes ASCII codepoints as single byte")
expect(utf8_encode_one(0x41)).to_equal([0x41])  # 'A'
expect(utf8_encode_one(0x00)).to_equal([0x00])
expect(utf8_encode_one(0x7F)).to_equal([0x7F])
```

</details>

#### encodes 2-byte codepoints

- encodes 2-byte codepoints
- Verify: encodes 2-byte codepoints
   - Expected: encoded.len() equals `2`
   - Expected: encoded[0] equals `0xC3`
   - Expected: encoded[1] equals `0xA9`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("encodes 2-byte codepoints")
step("Verify: encodes 2-byte codepoints")
# U+00E9 = e-acute = 0xC3 0xA9
val encoded = utf8_encode_one(0xE9)
expect(encoded.len()).to_equal(2)  # oracle: 2 — named expected value from the requirement
expect(encoded[0]).to_equal(0xC3)
expect(encoded[1]).to_equal(0xA9)
```

</details>

#### encodes 3-byte codepoints

- encodes 3-byte codepoints
- Verify: encodes 3-byte codepoints
   - Expected: encoded.len() equals `3`
   - Expected: encoded[0] equals `0xEA`
   - Expected: encoded[1] equals `0xB0`
   - Expected: encoded[2] equals `0x80`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("encodes 3-byte codepoints")
step("Verify: encodes 3-byte codepoints")
# U+AC00 = first Hangul syllable 가 = 0xEA 0xB0 0x80
val encoded = utf8_encode_one(0xAC00)
expect(encoded.len()).to_equal(3)  # oracle: 3 — named expected value from the requirement
expect(encoded[0]).to_equal(0xEA)
expect(encoded[1]).to_equal(0xB0)
expect(encoded[2]).to_equal(0x80)
```

</details>

#### encodes 4-byte codepoints

- encodes 4-byte codepoints
- Verify: encodes 4-byte codepoints
   - Expected: encoded.len() equals `4`
   - Expected: encoded[0] equals `0xF0`
   - Expected: encoded[1] equals `0x9F`
   - Expected: encoded[2] equals `0x98`
   - Expected: encoded[3] equals `0x80`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("encodes 4-byte codepoints")
step("Verify: encodes 4-byte codepoints")
# U+1F600 = grinning face emoji = 0xF0 0x9F 0x98 0x80
val encoded = utf8_encode_one(0x1F600)
expect(encoded.len()).to_equal(4)  # oracle: 4 — named expected value from the requirement
expect(encoded[0]).to_equal(0xF0)
expect(encoded[1]).to_equal(0x9F)
expect(encoded[2]).to_equal(0x98)
expect(encoded[3]).to_equal(0x80)
```

</details>

#### replaces surrogates with U+FFFD

- replaces surrogates with U+FFFD
- Verify: replaces surrogates with U+FFFD
   - Expected: encoded equals `[0xEF, 0xBF, 0xBD]`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("replaces surrogates with U+FFFD")
step("Verify: replaces surrogates with U+FFFD")
val encoded = utf8_encode_one(0xD800)
expect(encoded).to_equal([0xEF, 0xBF, 0xBD])
```

</details>

#### replaces out-of-range with U+FFFD

- replaces out-of-range with U+FFFD
- Verify: replaces out-of-range with U+FFFD
   - Expected: encoded equals `[0xEF, 0xBF, 0xBD]`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("replaces out-of-range with U+FFFD")
step("Verify: replaces out-of-range with U+FFFD")
val encoded = utf8_encode_one(0x110000)
expect(encoded).to_equal([0xEF, 0xBF, 0xBD])
```

</details>

#### replaces negative with U+FFFD

- replaces negative with U+FFFD
- Verify: replaces negative with U+FFFD
   - Expected: encoded equals `[0xEF, 0xBF, 0xBD]`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("replaces negative with U+FFFD")
step("Verify: replaces negative with U+FFFD")
val encoded = utf8_encode_one(-1)
expect(encoded).to_equal([0xEF, 0xBF, 0xBD])
```

</details>

### utf8_decode_one

#### decodes ASCII byte

- decodes ASCII byte
- Verify: decodes ASCII byte
   - Expected: result[0] equals `0x41`
   - Expected: result[1] equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("decodes ASCII byte")
step("Verify: decodes ASCII byte")
val result = utf8_decode_one([0x41], 0)
expect(result[0]).to_equal(0x41)
expect(result[1]).to_equal(1)  # oracle: 1 — named expected value from the requirement
```

</details>

#### decodes 2-byte sequence

- decodes 2-byte sequence
- Verify: decodes 2-byte sequence
   - Expected: result[0] equals `0xE9`
   - Expected: result[1] equals `2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("decodes 2-byte sequence")
step("Verify: decodes 2-byte sequence")
# U+00E9 = 0xC3 0xA9
val result = utf8_decode_one([0xC3, 0xA9], 0)
expect(result[0]).to_equal(0xE9)
expect(result[1]).to_equal(2)  # oracle: 2 — named expected value from the requirement
```

</details>

#### decodes 3-byte sequence for Korean

- decodes 3-byte sequence for Korean
- Verify: decodes 3-byte sequence for Korean
   - Expected: result[0] equals `0xAC00`
   - Expected: result[1] equals `3`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("decodes 3-byte sequence for Korean")
step("Verify: decodes 3-byte sequence for Korean")
# U+AC00 가 = 0xEA 0xB0 0x80
val result = utf8_decode_one([0xEA, 0xB0, 0x80], 0)
expect(result[0]).to_equal(0xAC00)
expect(result[1]).to_equal(3)  # oracle: 3 — named expected value from the requirement
```

</details>

#### decodes 4-byte sequence for emoji

- decodes 4-byte sequence for emoji
- Verify: decodes 4-byte sequence for emoji
   - Expected: result[0] equals `0x1F600`
   - Expected: result[1] equals `4`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("decodes 4-byte sequence for emoji")
step("Verify: decodes 4-byte sequence for emoji")
# U+1F600 = 0xF0 0x9F 0x98 0x80
val result = utf8_decode_one([0xF0, 0x9F, 0x98, 0x80], 0)
expect(result[0]).to_equal(0x1F600)
expect(result[1]).to_equal(4)  # oracle: 4 — named expected value from the requirement
```

</details>

#### returns replacement for continuation byte

- returns replacement for continuation byte
- Verify: returns replacement for continuation byte
   - Expected: result[0] equals `0xFFFD`
   - Expected: result[1] equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("returns replacement for continuation byte")
step("Verify: returns replacement for continuation byte")
val result = utf8_decode_one([0x80], 0)
expect(result[0]).to_equal(0xFFFD)
expect(result[1]).to_equal(1)  # oracle: 1 — named expected value from the requirement
```

</details>

#### returns replacement for truncated sequence

- returns replacement for truncated sequence
- Verify: returns replacement for truncated sequence
   - Expected: result[0] equals `0xFFFD`
   - Expected: result[1] equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("returns replacement for truncated sequence")
step("Verify: returns replacement for truncated sequence")
# 3-byte lead but only 2 bytes available
val result = utf8_decode_one([0xEA, 0xB0], 0)
expect(result[0]).to_equal(0xFFFD)
expect(result[1]).to_equal(1)  # oracle: 1 — named expected value from the requirement
```

</details>

#### rejects overlong 2-byte

- rejects overlong 2-byte
- Verify: rejects overlong 2-byte
   - Expected: result[0] equals `0xFFFD`
   - Expected: result[1] equals `2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("rejects overlong 2-byte")
step("Verify: rejects overlong 2-byte")
# Overlong: U+0041 encoded as 0xC1 0x81 (should be 1 byte)
val result = utf8_decode_one([0xC1, 0x81], 0)
expect(result[0]).to_equal(0xFFFD)
expect(result[1]).to_equal(2)  # oracle: 2 — named expected value from the requirement
```

</details>

#### returns error for out-of-bounds offset

- returns error for out-of-bounds offset
- Verify: returns error for out-of-bounds offset
   - Expected: result[0] equals `-1`
   - Expected: result[1] equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("returns error for out-of-bounds offset")
step("Verify: returns error for out-of-bounds offset")
val result = utf8_decode_one([0x41], 5)
expect(result[0]).to_equal(-1)  # oracle: -1 — named expected value from the requirement
expect(result[1]).to_equal(0)  # oracle: 0 — named expected value from the requirement
```

</details>

#### returns error for a negative offset

- returns error for a negative offset
- Exercise the lower offset bound independently
   - Expected: utf8_decode_one([0x41], -1) equals `[-1, 0]`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("returns error for a negative offset")
step("Exercise the lower offset bound independently")
expect(utf8_decode_one([0x41], -1)).to_equal([-1, 0])
```

</details>

#### rejects invalid two-byte payload values and continuation shape

- rejects invalid two-byte payload values and continuation shape
- Exercise numeric-range and continuation guards
   - Expected: utf8_decode_one([0xC2, -1], 0) equals `[0xFFFD, 1]`
   - Expected: utf8_decode_one([0xC2, 256], 0) equals `[0xFFFD, 1]`
   - Expected: utf8_decode_one([0xC2, 0x41], 0) equals `[0xFFFD, 1]`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("rejects invalid two-byte payload values and continuation shape")
step("Exercise numeric-range and continuation guards")
expect(utf8_decode_one([0xC2, -1], 0)).to_equal([0xFFFD, 1])
expect(utf8_decode_one([0xC2, 256], 0)).to_equal([0xFFFD, 1])
expect(utf8_decode_one([0xC2, 0x41], 0)).to_equal([0xFFFD, 1])
```

</details>

#### rejects malformed three-byte sequences

- rejects malformed three-byte sequences
- Exercise payload range, continuation, overlong, and surrogate guards
   - Expected: utf8_decode_one([0xE1, -1, 0x80], 0) equals `[0xFFFD, 1]`
   - Expected: utf8_decode_one([0xE1, 0x80, 256], 0) equals `[0xFFFD, 1]`
   - Expected: utf8_decode_one([0xE1, 0x41, 0x80], 0) equals `[0xFFFD, 1]`
   - Expected: utf8_decode_one([0xE0, 0x80, 0x80], 0) equals `[0xFFFD, 3]`
   - Expected: utf8_decode_one([0xED, 0xA0, 0x80], 0) equals `[0xFFFD, 3]`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("rejects malformed three-byte sequences")
step("Exercise payload range, continuation, overlong, and surrogate guards")
expect(utf8_decode_one([0xE1, -1, 0x80], 0)).to_equal([0xFFFD, 1])
expect(utf8_decode_one([0xE1, 0x80, 256], 0)).to_equal([0xFFFD, 1])
expect(utf8_decode_one([0xE1, 0x41, 0x80], 0)).to_equal([0xFFFD, 1])
expect(utf8_decode_one([0xE0, 0x80, 0x80], 0)).to_equal([0xFFFD, 3])
expect(utf8_decode_one([0xED, 0xA0, 0x80], 0)).to_equal([0xFFFD, 3])
```

</details>

#### rejects malformed four-byte sequences

- rejects malformed four-byte sequences
- Exercise payload range, continuation, overlong, and maximum guards
   - Expected: utf8_decode_one([0xF1, -1, 0x80, 0x80], 0) equals `[0xFFFD, 1]`
   - Expected: utf8_decode_one([0xF1, 0x80, 0x80, 256], 0) equals `[0xFFFD, 1]`
   - Expected: utf8_decode_one([0xF1, 0x80, 0x41, 0x80], 0) equals `[0xFFFD, 1]`
   - Expected: utf8_decode_one([0xF0, 0x80, 0x80, 0x80], 0) equals `[0xFFFD, 4]`
   - Expected: utf8_decode_one([0xF4, 0x90, 0x80, 0x80], 0) equals `[0xFFFD, 4]`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("rejects malformed four-byte sequences")
step("Exercise payload range, continuation, overlong, and maximum guards")
expect(utf8_decode_one([0xF1, -1, 0x80, 0x80], 0)).to_equal([0xFFFD, 1])
expect(utf8_decode_one([0xF1, 0x80, 0x80, 256], 0)).to_equal([0xFFFD, 1])
expect(utf8_decode_one([0xF1, 0x80, 0x41, 0x80], 0)).to_equal([0xFFFD, 1])
expect(utf8_decode_one([0xF0, 0x80, 0x80, 0x80], 0)).to_equal([0xFFFD, 4])
expect(utf8_decode_one([0xF4, 0x90, 0x80, 0x80], 0)).to_equal([0xFFFD, 4])
```

</details>

#### decodes at nonzero offset

- decodes at nonzero offset
- Verify: decodes at nonzero offset
   - Expected: result[0] equals `0x42`
   - Expected: result[1] equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("decodes at nonzero offset")
step("Verify: decodes at nonzero offset")
val result = utf8_decode_one([0x41, 0x42, 0x43], 1)
expect(result[0]).to_equal(0x42)
expect(result[1]).to_equal(1)  # oracle: 1 — named expected value from the requirement
```

</details>

### utf8_codepoint_byte_len

#### uses replacement width for negative and out-of-range values

- uses replacement width for negative and out-of-range values
- Exercise both invalid-range fallbacks
   - Expected: utf8_codepoint_byte_len(-1) equals `3`
   - Expected: utf8_codepoint_byte_len(0x110000) equals `3`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("uses replacement width for negative and out-of-range values")
step("Exercise both invalid-range fallbacks")
expect(utf8_codepoint_byte_len(-1)).to_equal(3)
expect(utf8_codepoint_byte_len(0x110000)).to_equal(3)
```

</details>

#### returns 1 for ASCII

- returns 1 for ASCII
- Verify: returns 1 for ASCII
   - Expected: utf8_codepoint_byte_len(0x41) equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("returns 1 for ASCII")
step("Verify: returns 1 for ASCII")
expect(utf8_codepoint_byte_len(0x41)).to_equal(1)  # oracle: 1 — named expected value from the requirement
```

</details>

#### returns 2 for Latin extended

- returns 2 for Latin extended
- Verify: returns 2 for Latin extended
   - Expected: utf8_codepoint_byte_len(0xE9) equals `2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("returns 2 for Latin extended")
step("Verify: returns 2 for Latin extended")
expect(utf8_codepoint_byte_len(0xE9)).to_equal(2)  # oracle: 2 — named expected value from the requirement
```

</details>

#### returns 3 for CJK and Hangul

- returns 3 for CJK and Hangul
- Verify: returns 3 for CJK and Hangul
   - Expected: utf8_codepoint_byte_len(0xAC00) equals `3`
   - Expected: utf8_codepoint_byte_len(0x4E00) equals `3`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("returns 3 for CJK and Hangul")
step("Verify: returns 3 for CJK and Hangul")
expect(utf8_codepoint_byte_len(0xAC00)).to_equal(3)  # oracle: 3 — named expected value from the requirement
expect(utf8_codepoint_byte_len(0x4E00)).to_equal(3)  # oracle: 3 — named expected value from the requirement
```

</details>

#### returns 4 for supplementary planes

- returns 4 for supplementary planes
- Verify: returns 4 for supplementary planes
   - Expected: utf8_codepoint_byte_len(0x1F600) equals `4`
   - Expected: utf8_codepoint_byte_len(0x10FFFF) equals `4`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("returns 4 for supplementary planes")
step("Verify: returns 4 for supplementary planes")
expect(utf8_codepoint_byte_len(0x1F600)).to_equal(4)  # oracle: 4 — named expected value from the requirement
expect(utf8_codepoint_byte_len(0x10FFFF)).to_equal(4)  # oracle: 4 — named expected value from the requirement
```

</details>

### utf8_encode_all and utf8_decode_all

#### roundtrips ASCII

- roundtrips ASCII
- Verify: roundtrips ASCII
   - Expected: decoded equals `cps`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("roundtrips ASCII")
step("Verify: roundtrips ASCII")
val cps = [0x48, 0x65, 0x6C, 0x6C, 0x6F]  # "Hello"
val encoded = utf8_encode_all(cps)
val decoded = utf8_decode_all(encoded)
expect(decoded).to_equal(cps)
```

</details>

#### roundtrips Korean

- roundtrips Korean
- Verify: roundtrips Korean
   - Expected: encoded.len() equals `9`
   - Expected: decoded equals `cps`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("roundtrips Korean")
step("Verify: roundtrips Korean")
# 가나다 = U+AC00 U+B098 U+B2E4
val cps = [0xAC00, 0xB098, 0xB2E4]
val encoded = utf8_encode_all(cps)
expect(encoded.len()).to_equal(9)  # oracle: 9 — named expected value from the requirement
val decoded = utf8_decode_all(encoded)
expect(decoded).to_equal(cps)
```

</details>

#### roundtrips mixed ASCII and emoji

- roundtrips mixed ASCII and emoji
- Verify: roundtrips mixed ASCII and emoji
   - Expected: encoded.len() equals `6`
   - Expected: decoded equals `cps`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("roundtrips mixed ASCII and emoji")
step("Verify: roundtrips mixed ASCII and emoji")
# "Hi" + U+1F600
val cps = [0x48, 0x69, 0x1F600]
val encoded = utf8_encode_all(cps)
expect(encoded.len()).to_equal(6)  # oracle: 6 — named expected value from the requirement
val decoded = utf8_decode_all(encoded)
expect(decoded).to_equal(cps)
```

</details>

#### roundtrips Cyrillic

- roundtrips Cyrillic
- Verify: roundtrips Cyrillic
   - Expected: decoded equals `cps`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("roundtrips Cyrillic")
step("Verify: roundtrips Cyrillic")
# Привет = U+041F U+0440 U+0438 U+0432 U+0435 U+0442
val cps = [0x041F, 0x0440, 0x0438, 0x0432, 0x0435, 0x0442]
val encoded = utf8_encode_all(cps)
val decoded = utf8_decode_all(encoded)
expect(decoded).to_equal(cps)
```

</details>

#### roundtrips Arabic

- roundtrips Arabic
- Verify: roundtrips Arabic
   - Expected: decoded equals `cps`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("roundtrips Arabic")
step("Verify: roundtrips Arabic")
# مرحبا = U+0645 U+0631 U+062D U+0628 U+0627
val cps = [0x0645, 0x0631, 0x062D, 0x0628, 0x0627]
val encoded = utf8_encode_all(cps)
val decoded = utf8_decode_all(encoded)
expect(decoded).to_equal(cps)
```

</details>

#### roundtrips Japanese Hiragana

- roundtrips Japanese Hiragana
- Verify: roundtrips Japanese Hiragana
   - Expected: decoded equals `cps`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("roundtrips Japanese Hiragana")
step("Verify: roundtrips Japanese Hiragana")
# こんにちは = U+3053 U+3093 U+306B U+3061 U+306F
val cps = [0x3053, 0x3093, 0x306B, 0x3061, 0x306F]
val encoded = utf8_encode_all(cps)
val decoded = utf8_decode_all(encoded)
expect(decoded).to_equal(cps)
```

</details>

#### roundtrips Chinese

- roundtrips Chinese
- Verify: roundtrips Chinese
   - Expected: encoded.len() equals `6`
   - Expected: decoded equals `cps`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("roundtrips Chinese")
step("Verify: roundtrips Chinese")
# 你好 = U+4F60 U+597D
val cps = [0x4F60, 0x597D]
val encoded = utf8_encode_all(cps)
expect(encoded.len()).to_equal(6)  # oracle: 6 — named expected value from the requirement
val decoded = utf8_decode_all(encoded)
expect(decoded).to_equal(cps)
```

</details>

#### roundtrips Devanagari

- roundtrips Devanagari
- Verify: roundtrips Devanagari
   - Expected: decoded equals `cps`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("roundtrips Devanagari")
step("Verify: roundtrips Devanagari")
# नमस्ते = U+0928 U+092E U+0938 U+094D U+0924 U+0947
val cps = [0x0928, 0x092E, 0x0938, 0x094D, 0x0924, 0x0947]
val encoded = utf8_encode_all(cps)
val decoded = utf8_decode_all(encoded)
expect(decoded).to_equal(cps)
```

</details>

#### handles empty input

- handles empty input
- Verify: handles empty input
   - Expected: encoded.len() equals `0`
   - Expected: decoded.len() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("handles empty input")
step("Verify: handles empty input")
val encoded = utf8_encode_all([])
expect(encoded.len()).to_equal(0)  # oracle: 0 — named expected value from the requirement
val decoded = utf8_decode_all([])
expect(decoded.len()).to_equal(0)  # oracle: 0 — named expected value from the requirement
```

</details>

### codepoint counting via decode_all

#### counts ASCII bytes

- counts ASCII bytes
- Verify: counts ASCII bytes
   - Expected: decoded.len() equals `5`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("counts ASCII bytes")
step("Verify: counts ASCII bytes")
val decoded = utf8_decode_all([0x48, 0x65, 0x6C, 0x6C, 0x6F])
expect(decoded.len()).to_equal(5)  # oracle: 5 — named expected value from the requirement
```

</details>

#### counts Korean 3-byte sequences

- counts Korean 3-byte sequences
- Verify: counts Korean 3-byte sequences
   - Expected: decoded.len() equals `3`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("counts Korean 3-byte sequences")
step("Verify: counts Korean 3-byte sequences")
val bytes = utf8_encode_all([0xAC00, 0xB098, 0xB2E4])
val decoded = utf8_decode_all(bytes)
expect(decoded.len()).to_equal(3)  # oracle: 3 — named expected value from the requirement
```

</details>

#### counts emoji 4-byte sequences

- counts emoji 4-byte sequences
- Verify: counts emoji 4-byte sequences
   - Expected: decoded.len() equals `2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("counts emoji 4-byte sequences")
step("Verify: counts emoji 4-byte sequences")
val bytes = utf8_encode_all([0x1F600, 0x1F601])
val decoded = utf8_decode_all(bytes)
expect(decoded.len()).to_equal(2)  # oracle: 2 — named expected value from the requirement
```

</details>

#### counts empty

- counts empty
- Verify: counts empty
   - Expected: decoded.len() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("counts empty")
step("Verify: counts empty")
val decoded = utf8_decode_all([])
expect(decoded.len()).to_equal(0)  # oracle: 0 — named expected value from the requirement
```

</details>

### text_byte_len

#### returns byte length of ASCII text

- returns byte length of ASCII text
- Verify: returns byte length of ASCII text
   - Expected: text_byte_len("Hello") equals `5`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("returns byte length of ASCII text")
step("Verify: returns byte length of ASCII text")
expect(text_byte_len("Hello")).to_equal(5)
```

</details>

#### returns byte length of empty text

- returns byte length of empty text
- Verify: returns byte length of empty text
   - Expected: text_byte_len("") equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("returns byte length of empty text")
step("Verify: returns byte length of empty text")
expect(text_byte_len("")).to_equal(0)
```

</details>

### text_codepoints length

#### returns codepoint count for ASCII

- returns codepoint count for ASCII
- Verify: returns codepoint count for ASCII
   - Expected: cps.len() equals `5`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("returns codepoint count for ASCII")
step("Verify: returns codepoint count for ASCII")
val cps = text_codepoints("Hello")
expect(cps.len()).to_equal(5)  # oracle: 5 — named expected value from the requirement
```

</details>

### text_without_last_codepoint

#### removes exactly one trailing UTF-8 scalar

- removes exactly one trailing UTF-8 scalar
- Verify: removes exactly one trailing UTF-8 scalar
   - Expected: text_without_last_codepoint("") equals ``
   - Expected: text_without_last_codepoint("abc") equals `ab`
   - Expected: text_without_last_codepoint("한é") equals `한`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("removes exactly one trailing UTF-8 scalar")
step("Verify: removes exactly one trailing UTF-8 scalar")
expect(text_without_last_codepoint("")).to_equal("")
expect(text_without_last_codepoint("abc")).to_equal("ab")
expect(text_without_last_codepoint("한é")).to_equal("한")
```

</details>

### text_codepoints

#### returns codepoints for ASCII

- returns codepoints for ASCII
- Verify: returns codepoints for ASCII
   - Expected: cps.len() equals `3`
   - Expected: cps[0] equals `0x41`
   - Expected: cps[1] equals `0x42`
   - Expected: cps[2] equals `0x43`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("returns codepoints for ASCII")
step("Verify: returns codepoints for ASCII")
val cps = text_codepoints("ABC")
expect(cps.len()).to_equal(3)  # oracle: 3 — named expected value from the requirement
expect(cps[0]).to_equal(0x41)
expect(cps[1]).to_equal(0x42)
expect(cps[2]).to_equal(0x43)
```

</details>

### char_from_codepoint

#### converts ASCII codepoint to text

- converts ASCII codepoint to text
- Verify: converts ASCII codepoint to text
   - Expected: char_from_codepoint(0x41) equals `A`
   - Expected: char_from_codepoint(0x30) equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("converts ASCII codepoint to text")
step("Verify: converts ASCII codepoint to text")
expect(char_from_codepoint(0x41)).to_equal("A")
expect(char_from_codepoint(0x30)).to_equal("0")
```

</details>

### text_from_codepoints

#### creates text from ASCII codepoints

- creates text from ASCII codepoints
- Verify: creates text from ASCII codepoints
   - Expected: result equals `Hi`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("creates text from ASCII codepoints")
step("Verify: creates text from ASCII codepoints")
val result = text_from_codepoints([0x48, 0x69])
expect(result).to_equal("Hi")
```

</details>

#### creates text through both ASCII and multibyte paths

- creates text through both ASCII and multibyte paths
- Exercise both text construction branches
   - Expected: text_from_codepoints([0x41, 0x00E9, 0xD55C, 0x1F600]) equals `Aé한😀`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("creates text through both ASCII and multibyte paths")
step("Exercise both text construction branches")
expect(text_from_codepoints([0x41, 0x00E9, 0xD55C, 0x1F600])).to_equal("Aé한😀")
```

</details>

### char_from_code encodes scalars above 127

#### encodes U+00A2 as the cent sign, not U+FFFD

- encodes U+00A2 as the cent sign, not U+FFFD
- Verify: encodes U+00A2 as the cent sign, not U+FFFD
   - Expected: char_from_code(0xA2) equals `¢`
   - Expected: char_from_code(0xA2).len() equals `2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("encodes U+00A2 as the cent sign, not U+FFFD")
step("Verify: encodes U+00A2 as the cent sign, not U+FFFD")
expect(char_from_code(0xA2)).to_equal("¢")
expect(char_from_code(0xA2).len()).to_equal(2)
```

</details>

#### encodes the 2, 3 and 4 byte boundaries

- encodes the 2, 3 and 4 byte boundaries
- Verify: encodes the 2, 3 and 4 byte boundaries
   - Expected: char_from_code(128).len() equals `2`
   - Expected: char_from_code(0x7FF).len() equals `2`
   - Expected: char_from_code(0x800).len() equals `3`
   - Expected: char_from_code(0xD55C) equals `한`
   - Expected: char_from_code(0xFFFF).len() equals `3`
   - Expected: char_from_code(0x10000).len() equals `4`
   - Expected: char_from_code(0x1F600) equals `😀`
   - Expected: char_from_code(0x10FFFF).len() equals `4`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("encodes the 2, 3 and 4 byte boundaries")
step("Verify: encodes the 2, 3 and 4 byte boundaries")
expect(char_from_code(128).len()).to_equal(2)
expect(char_from_code(0x7FF).len()).to_equal(2)
expect(char_from_code(0x800).len()).to_equal(3)
expect(char_from_code(0xD55C)).to_equal("한")
expect(char_from_code(0xFFFF).len()).to_equal(3)
expect(char_from_code(0x10000).len()).to_equal(4)
expect(char_from_code(0x1F600)).to_equal("😀")
expect(char_from_code(0x10FFFF).len()).to_equal(4)
```

</details>

#### keeps ASCII unchanged

- keeps ASCII unchanged
- Verify: keeps ASCII unchanged
   - Expected: char_from_code(65) equals `A`
   - Expected: char_from_code(0x7F).len() equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("keeps ASCII unchanged")
step("Verify: keeps ASCII unchanged")
expect(char_from_code(65)).to_equal("A")
expect(char_from_code(0x7F).len()).to_equal(1)
```

</details>

#### yields U+FFFD for surrogates and out-of-range values

- yields U+FFFD for surrogates and out-of-range values
- Verify: yields U+FFFD for surrogates and out-of-range values
   - Expected: char_from_code(0xD800) equals `\uFFFD`
   - Expected: char_from_code(0xDFFF) equals `\uFFFD`
   - Expected: char_from_code(0x110000) equals `\uFFFD`
   - Expected: char_from_code(-1) equals `\uFFFD`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("yields U+FFFD for surrogates and out-of-range values")
step("Verify: yields U+FFFD for surrogates and out-of-range values")
expect(char_from_code(0xD800)).to_equal("\uFFFD")
expect(char_from_code(0xDFFF)).to_equal("\uFFFD")
expect(char_from_code(0x110000)).to_equal("\uFFFD")
expect(char_from_code(-1)).to_equal("\uFFFD")
```

</details>

#### agrees byte-for-byte with std.string_core for every valid scalar

- agrees byte-for-byte with std.string_core for every valid scalar
- Verify: agrees byte-for-byte with std.string_core for every valid scalar
   - Expected: char_from_code(cp) equals `char_from_code_inline(cp)`
   - Expected: char_from_code(cp).len() equals `char_from_code_inline(cp).len()`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("agrees byte-for-byte with std.string_core for every valid scalar")
step("Verify: agrees byte-for-byte with std.string_core for every valid scalar")
for cp in [0, 9, 10, 32, 65, 0x7F, 128, 0xA2, 0x7FF, 0x800, 0xD55C, 0xD7FF, 0xE000, 0xFFFF, 0x10000, 0x1F600, 0x10FFFF]:
    expect(char_from_code(cp)).to_equal(char_from_code_inline(cp))
    expect(char_from_code(cp).len()).to_equal(char_from_code_inline(cp).len())
```

</details>

#### documents the one policy difference: string_core returns empty text for invalid input

- documents the one policy difference: string_core returns empty text for invalid input
- Verify: string_core returns empty text for invalid input
   - Expected: char_from_code_inline(0xD800) equals ``
   - Expected: char_from_code_inline(0x110000) equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("documents the one policy difference: string_core returns empty text for invalid input")
step("Verify: string_core returns empty text for invalid input")
expect(char_from_code_inline(0xD800)).to_equal("")
expect(char_from_code_inline(0x110000)).to_equal("")
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 58 |
| Active scenarios | 58 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-LIB`
- `REQ-LIB-COMMON-001`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `de292197009bd189d8fc0ce982118319367fc13cca3dc124c583799c6e1a21d6`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `de292197009bd189d8fc0ce982118319367fc13cca3dc124c583799c6e1a21d6`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `de292197009bd189d8fc0ce982118319367fc13cca3dc124c583799c6e1a21d6`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **86/100**; effective score: **86/100**; blockers: **0**.

SSpec documentization score: 86/100
source: test/01_unit/lib/common/encoding/utf8_spec.spl
mirror: doc/06_spec/01_unit/lib/common/encoding/utf8_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/lib/common/encoding/utf8_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/lib/common/encoding/utf8_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/lib/common/encoding/utf8_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 12 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/lib/common/encoding/utf8_spec.spl:43:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'returns 1 for ASCII bytes' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/common/encoding/utf8_spec.spl:52:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'returns 0 for continuation bytes' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/common/encoding/utf8_spec.spl:59:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'returns 2 for 2-byte lead' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
