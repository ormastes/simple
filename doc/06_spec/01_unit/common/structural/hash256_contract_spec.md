# Hash256 Contract Specification

> Tests covering Hash256 frozen widths, Hash256 hex alphabet, Hash256 EXACT BYTES against hand-derived golden vectors, Hash256 as an embedded field, Hash256 byte accessor, Hash256 round trip, Hash256 REJECTION — spellings the contract refuses, Hash256 buffer rejection.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 29 | 29 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Hash256 Contract Specification

## Scenarios

### Hash256 frozen widths

#### pins 32 wire bytes and 64 host characters

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- pins 32 wire bytes and 64 host characters


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("pins 32 wire bytes and 64 host characters")
assert_equal(HASH256_LEN, 32)
assert_equal(HASH256_HEX_LEN, 64)
assert_equal(hash256_hex_len(), 64)
```

</details>

#### pins the zero digest as 64 zero characters, not an absence sentinel

- pins the zero digest as 64 zero characters, not an absence sentinel


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("pins the zero digest as 64 zero characters, not an absence sentinel")
assert_equal(HASH256_ZERO.len(), 64)
assert_equal(HASH256_ZERO, GOLDEN_HASH256_ZERO_HEX)
assert_true(hash256_is_zero(HASH256_ZERO))
assert_false(hash256_is_zero(GOLDEN_HASH256_ONES_HEX))
# A legal digest that happens to be zero is still a digest: the zero
# value MUST encode, so it cannot double as "no digest".
assert_true(encode_hash256(HASH256_ZERO).ok)
```

</details>

### Hash256 hex alphabet

#### decodes 0-9 and a-f and nothing else

- decodes 0-9 and a-f and nothing else


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("decodes 0-9 and a-f and nothing else")
assert_equal(hash256_hex_nibble(48), 0)
assert_equal(hash256_hex_nibble(57), 9)
assert_equal(hash256_hex_nibble(97), 10)
assert_equal(hash256_hex_nibble(102), 15)
```

</details>

#### rejects uppercase A-F rather than folding them

- rejects uppercase A-F rather than folding them


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rejects uppercase A-F rather than folding them")
assert_equal(hash256_hex_nibble(65), 0 - 1)
assert_equal(hash256_hex_nibble(70), 0 - 1)
```

</details>

#### rejects the characters immediately outside each range

- rejects the characters immediately outside each range


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rejects the characters immediately outside each range")
assert_equal(hash256_hex_nibble(47), 0 - 1)
assert_equal(hash256_hex_nibble(58), 0 - 1)
assert_equal(hash256_hex_nibble(96), 0 - 1)
assert_equal(hash256_hex_nibble(103), 0 - 1)
```

</details>

#### renders a byte as two lowercase characters, masked to 8 bits

- renders a byte as two lowercase characters, masked to 8 bits


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("renders a byte as two lowercase characters, masked to 8 bits")
assert_equal(hash256_hex_of_byte(0), "00")
assert_equal(hash256_hex_of_byte(1), "01")
assert_equal(hash256_hex_of_byte(15), "0f")
assert_equal(hash256_hex_of_byte(128), "80")
assert_equal(hash256_hex_of_byte(255), "ff")
# A sign-extended i64 must not widen the spelling.
assert_equal(hash256_hex_of_byte(0 - 1), "ff")
assert_equal(hash256_hex_of_byte(256), "00")
```

</details>

### Hash256 EXACT BYTES against hand-derived golden vectors

#### encodes the zero digest as 32 zero bytes

- encodes the zero digest as 32 zero bytes


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("encodes the zero digest as 32 zero bytes")
assert_equal(encoded_hex(GOLDEN_HASH256_ZERO_HEX),
             GOLDEN_HASH256_ZERO_BYTES)
```

</details>

#### encodes the all-ones digest as 32 0xff bytes

- encodes the all-ones digest as 32 0xff bytes


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("encodes the all-ones digest as 32 0xff bytes")
assert_equal(encoded_hex(GOLDEN_HASH256_ONES_HEX),
             GOLDEN_HASH256_ONES_BYTES)
```

</details>

#### encodes the ascending ladder in digest order, high nibble first

- encodes the ascending ladder in digest order, high nibble first


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("encodes the ascending ladder in digest order, high nibble first")
# THE byte-order vector. All 32 bytes distinct, so any permutation of
# the positions changes this string.
assert_equal(encoded_hex(GOLDEN_HASH256_LADDER_ASC_HEX),
             GOLDEN_HASH256_LADDER_ASC_BYTES)
```

</details>

#### is NOT the four-little-endian-u64-halves layout

- is NOT the four-little-endian-u64-halves layout


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("is NOT the four-little-endian-u64-halves layout")
# The layout Hash128 uses, spelled out. If hash256_put ever routes
# through wire_put_u64 this assertion is the one that fires; the
# round-trip assertions below would not notice.
assert_false(encoded_hex(GOLDEN_HASH256_LADDER_ASC_HEX)
             == "0706050403020100"
                + "0f0e0d0c0b0a0908"
                + "1716151413121110"
                + "1f1e1d1c1b1a1918")
```

</details>

#### encodes the descending ladder, distinguishing a whole-run reversal

- encodes the descending ladder, distinguishing a whole-run reversal


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("encodes the descending ladder, distinguishing a whole-run reversal")
assert_equal(encoded_hex(GOLDEN_HASH256_LADDER_DESC_HEX),
             GOLDEN_HASH256_LADDER_DESC_BYTES)
```

</details>

#### encodes the high-bit digest with no sign extension and no end swap

- encodes the high-bit digest with no sign extension and no end swap


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("encodes the high-bit digest with no sign extension and no end swap")
assert_equal(encoded_hex(GOLDEN_HASH256_HIGH_BIT_HEX),
             GOLDEN_HASH256_HIGH_BIT_BYTES)
```

</details>

#### emits exactly 32 bytes for every vector

- emits exactly 32 bytes for every vector


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("emits exactly 32 bytes for every vector")
assert_equal(encode_hash256(GOLDEN_HASH256_ZERO_HEX).bytes.len(), 32)
assert_equal(encode_hash256(GOLDEN_HASH256_ONES_HEX).bytes.len(), 32)
assert_equal(
    encode_hash256(GOLDEN_HASH256_LADDER_ASC_HEX).bytes.len(), 32)
assert_equal(
    encode_hash256(GOLDEN_HASH256_HIGH_BIT_HEX).bytes.len(), 32)
```

</details>

### Hash256 as an embedded field

#### follows a u32 with no length prefix, envelope or alignment padding

- follows a u32 with no length prefix, envelope or alignment padding


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("follows a u32 with no length prefix, envelope or alignment padding")
var b: [u8] = []
b = wire_put_u32(b, GOLDEN_HASH256_EMBEDDED_PREFIX_U32)
b = hash256_put(b, GOLDEN_HASH256_LADDER_ASC_HEX)
assert_equal(wire_to_hex(b), GOLDEN_HASH256_EMBEDDED_BYTES)
assert_equal(b.len(), 36)
```

</details>

#### reads back from a non-zero offset

- reads back from a non-zero offset


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("reads back from a non-zero offset")
var b: [u8] = []
b = wire_put_u32(b, GOLDEN_HASH256_EMBEDDED_PREFIX_U32)
b = hash256_put(b, GOLDEN_HASH256_LADDER_ASC_HEX)
assert_equal(hash256_read(b, 4), GOLDEN_HASH256_LADDER_ASC_HEX)
```

</details>

#### bounds a region in i64, so a large offset cannot wrap into 'fits'

- bounds a region in i64, so a large offset cannot wrap into 'fits'


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("bounds a region in i64, so a large offset cannot wrap into 'fits'")
var b: [u8] = []
b = wire_put_u32(b, GOLDEN_HASH256_EMBEDDED_PREFIX_U32)
b = hash256_put(b, GOLDEN_HASH256_LADDER_ASC_HEX)
assert_true(hash256_region_valid(b, 4))
assert_false(hash256_region_valid(b, 5))
assert_false(hash256_region_valid(b, 0 - 1))
# 2^32 - 1: at 32-bit width `off + 32` wraps to 31 and reads as
# in-range. Computed in i64 it does not.
assert_false(hash256_region_valid(b, 4294967295))
```

</details>

### Hash256 byte accessor

#### maps byte i to characters 2i and 2i+1, high nibble first

- maps byte i to characters 2i and 2i+1, high nibble first


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("maps byte i to characters 2i and 2i+1, high nibble first")
assert_equal(hash256_byte(GOLDEN_HASH256_LADDER_ASC_HEX, 0), 0)
assert_equal(hash256_byte(GOLDEN_HASH256_LADDER_ASC_HEX, 1), 1)
assert_equal(hash256_byte(GOLDEN_HASH256_LADDER_ASC_HEX, 16), 16)
assert_equal(hash256_byte(GOLDEN_HASH256_LADDER_ASC_HEX, 31), 31)
assert_equal(hash256_byte(GOLDEN_HASH256_HIGH_BIT_HEX, 0), 128)
assert_equal(hash256_byte(GOLDEN_HASH256_HIGH_BIT_HEX, 31), 1)
```

</details>

#### refuses an out-of-range index rather than reading past the spelling

- refuses an out-of-range index rather than reading past the spelling


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("refuses an out-of-range index rather than reading past the spelling")
assert_equal(hash256_byte(GOLDEN_HASH256_LADDER_ASC_HEX, 32), 0 - 1)
assert_equal(hash256_byte(GOLDEN_HASH256_LADDER_ASC_HEX, 0 - 1),
             0 - 1)
```

</details>

### Hash256 round trip

#### reconstructs every vector through encode then decode

- reconstructs every vector through encode then decode


<details>
<summary>Executable SSpec</summary>

Runnable source: 17 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("reconstructs every vector through encode then decode")
assert_equal(decode_hash256(
    encode_hash256(GOLDEN_HASH256_ZERO_HEX).bytes).value,
    GOLDEN_HASH256_ZERO_HEX)
assert_equal(decode_hash256(
    encode_hash256(GOLDEN_HASH256_ONES_HEX).bytes).value,
    GOLDEN_HASH256_ONES_HEX)
assert_equal(decode_hash256(
    encode_hash256(GOLDEN_HASH256_LADDER_ASC_HEX).bytes).value,
    GOLDEN_HASH256_LADDER_ASC_HEX)
assert_equal(decode_hash256(
    encode_hash256(GOLDEN_HASH256_LADDER_DESC_HEX).bytes).value,
    GOLDEN_HASH256_LADDER_DESC_HEX)
assert_equal(decode_hash256(
    encode_hash256(GOLDEN_HASH256_HIGH_BIT_HEX).bytes).value,
    GOLDEN_HASH256_HIGH_BIT_HEX)
```

</details>

### Hash256 REJECTION — spellings the contract refuses

#### accepts exactly the frozen spelling

- accepts exactly the frozen spelling


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("accepts exactly the frozen spelling")
assert_true(hash256_hex_valid(GOLDEN_HASH256_ZERO_HEX))
assert_true(hash256_hex_valid(GOLDEN_HASH256_ONES_HEX))
assert_true(hash256_hex_valid(GOLDEN_HASH256_LADDER_ASC_HEX))
assert_true(hash256_hex_valid(GOLDEN_HASH256_LADDER_DESC_HEX))
assert_true(hash256_hex_valid(GOLDEN_HASH256_HIGH_BIT_HEX))
```

</details>

#### rejects uppercase rather than folding it to one encoding

- rejects uppercase rather than folding it to one encoding


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rejects uppercase rather than folding it to one encoding")
assert_false(hash256_hex_valid(GOLDEN_HASH256_REJECT_UPPERCASE))
assert_false(encode_hash256(GOLDEN_HASH256_REJECT_UPPERCASE).ok)
assert_equal(
    encode_hash256(GOLDEN_HASH256_REJECT_UPPERCASE).bytes.len(), 0)
```

</details>

#### rejects mixed case, which a naive to_lower fold would let past

- rejects mixed case, which a naive to_lower fold would let past


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rejects mixed case, which a naive to_lower fold would let past")
assert_false(hash256_hex_valid(GOLDEN_HASH256_REJECT_MIXED_CASE))
assert_false(encode_hash256(GOLDEN_HASH256_REJECT_MIXED_CASE).ok)
```

</details>

#### rejects a 63-character spelling instead of encoding a short field

- rejects a 63-character spelling instead of encoding a short field


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rejects a 63-character spelling instead of encoding a short field")
assert_equal(GOLDEN_HASH256_REJECT_SHORT.len(), 63)
assert_false(hash256_hex_valid(GOLDEN_HASH256_REJECT_SHORT))
assert_false(encode_hash256(GOLDEN_HASH256_REJECT_SHORT).ok)
```

</details>

#### rejects a 66-character spelling instead of truncating it

- rejects a 66-character spelling instead of truncating it


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rejects a 66-character spelling instead of truncating it")
assert_equal(GOLDEN_HASH256_REJECT_LONG.len(), 66)
assert_false(hash256_hex_valid(GOLDEN_HASH256_REJECT_LONG))
assert_false(encode_hash256(GOLDEN_HASH256_REJECT_LONG).ok)
```

</details>

#### rejects a non-hex character just past the alphabet

- rejects a non-hex character just past the alphabet


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rejects a non-hex character just past the alphabet")
assert_false(hash256_hex_valid(GOLDEN_HASH256_REJECT_NON_HEX))
assert_false(encode_hash256(GOLDEN_HASH256_REJECT_NON_HEX).ok)
```

</details>

#### rejects the empty and free-form spellings that exist in tree today

- rejects the empty and free-form spellings that exist in tree today


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rejects the empty and free-form spellings that exist in tree today")
# receipt_types.spl initialises input_hash to "" and
# staged_backend.spl writes Hash256(value: "staged_empty"). Both are
# refused: this is a real migration, recorded in the contract document.
assert_false(hash256_hex_valid(GOLDEN_HASH256_REJECT_EMPTY))
assert_false(encode_hash256(GOLDEN_HASH256_REJECT_EMPTY).ok)
assert_false(hash256_hex_valid(GOLDEN_HASH256_REJECT_FREEFORM))
assert_false(encode_hash256(GOLDEN_HASH256_REJECT_FREEFORM).ok)
```

</details>

### Hash256 buffer rejection

#### requires exactly 32 bytes

- requires exactly 32 bytes


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("requires exactly 32 bytes")
val good = encode_hash256(GOLDEN_HASH256_LADDER_ASC_HEX).bytes
assert_true(decode_hash256(good).ok)
assert_false(decode_hash256(truncated(good, 31)).ok)
assert_false(decode_hash256(appended(good, 0)).ok)
```

</details>

#### rejects an empty buffer rather than returning the zero digest

- rejects an empty buffer rather than returning the zero digest


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rejects an empty buffer rather than returning the zero digest")
val empty: [u8] = []
assert_false(decode_hash256(empty).ok)
assert_equal(decode_hash256(empty).value, "")
```

</details>

#### returns a non-digest value on refusal, so ignoring ok cannot smuggle

- returns a non-digest value on refusal, so ignoring ok cannot smuggle


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns a non-digest value on refusal, so ignoring ok cannot smuggle")
assert_false(hash256_hex_valid(decode_hash256(
    encode_hash256(GOLDEN_HASH256_REJECT_UPPERCASE).bytes).value))
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/01_unit/common/structural/hash256_contract_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering Hash256 frozen widths, Hash256 hex alphabet, Hash256 EXACT BYTES against hand-derived golden vectors, Hash256 as an embedded field, Hash256 byte accessor, Hash256 round trip, Hash256 REJECTION — spellings the contract refuses, Hash256 buffer rejection.
- Hash256 frozen widths
- Hash256 hex alphabet
- Hash256 EXACT BYTES against hand-derived golden vectors
- Hash256 as an embedded field
- Hash256 byte accessor
- Hash256 round trip
- Hash256 REJECTION — spellings the contract refuses
- Hash256 buffer rejection

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 29 |
| Active scenarios | 29 |
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

- Canonical SPipe generation for source `18b2148d5d13cc0237df41eca103fae23d784c0f0dfa2425de7dfb5de53def14`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `18b2148d5d13cc0237df41eca103fae23d784c0f0dfa2425de7dfb5de53def14`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `18b2148d5d13cc0237df41eca103fae23d784c0f0dfa2425de7dfb5de53def14`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/01_unit/common/structural/hash256_contract_spec.spl
mirror: doc/06_spec/01_unit/common/structural/hash256_contract_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/common/structural/hash256_contract_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/common/structural/hash256_contract_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/common/structural/hash256_contract_spec.spl:105:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'pins 32 wire bytes and 64 host characters' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/common/structural/hash256_contract_spec.spl:112:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'pins the zero digest as 64 zero characters, not an absence sentinel' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/common/structural/hash256_contract_spec.spl:124:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'decodes 0-9 and a-f and nothing else' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
