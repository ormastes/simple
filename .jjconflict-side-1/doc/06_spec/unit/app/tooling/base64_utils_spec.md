# Base64 Utils Specification

> Tests covering Base64 Utilities, Alphabet, Character Conversion, Find Index, Encoding, Decoding, URL-Safe Encoding, Validation, Round-trip.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 35 | 35 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Base64 Utils Specification

## Scenarios

### Base64 Utilities

### Alphabet

#### has 64 characters

- has 64 characters


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("has 64 characters")
val alphabet = base64_alphabet()
expect alphabet.len() == 64
```

</details>

#### starts with ABC

- starts with ABC


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("starts with ABC")
val alphabet = base64_alphabet()
expect alphabet.starts_with("ABC")
```

</details>

#### ends with +/

- ends with +/


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("ends with +/")
val alphabet = base64_alphabet()
expect alphabet.ends_with("+/")
```

</details>

### Character Conversion

#### converts letters to bytes

- converts letters to bytes


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("converts letters to bytes")
expect char_to_byte("A") == 65
expect char_to_byte("B") == 66
expect char_to_byte("a") == 97
expect char_to_byte("b") == 98
```

</details>

#### converts digits to bytes

- converts digits to bytes


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("converts digits to bytes")
expect char_to_byte("0") == 48
expect char_to_byte("1") == 49
expect char_to_byte("2") == 50
```

</details>

#### converts special chars to bytes

- converts special chars to bytes


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("converts special chars to bytes")
expect char_to_byte(" ") == 32
expect char_to_byte("!") == 33
```

</details>

#### converts bytes to letters

- converts bytes to letters


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("converts bytes to letters")
expect byte_to_char(65) == "A"
expect byte_to_char(66) == "B"
expect byte_to_char(97) == "a"
```

</details>

#### converts bytes to digits

- converts bytes to digits


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("converts bytes to digits")
expect byte_to_char(48) == "0"
expect byte_to_char(49) == "1"
```

</details>

#### returns ? for unknown bytes

- returns ? for unknown bytes


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns ? for unknown bytes")
expect byte_to_char(255) == "?"
```

</details>

### Find Index

#### finds A at index 0

- finds A at index 0


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("finds A at index 0")
val alphabet = base64_alphabet()
match find_base64_index(c = "A", alphabet = alphabet):
    case Some(idx): expect idx == 0
    case nil: expect false
```

</details>

#### finds a at index 26

- finds a at index 26


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("finds a at index 26")
val alphabet = base64_alphabet()
match find_base64_index(c = "a", alphabet = alphabet):
    case Some(idx): expect idx == 26
    case nil: expect false
```

</details>

#### finds / at index 63

- finds / at index 63


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("finds / at index 63")
val alphabet = base64_alphabet()
match find_base64_index(c = "/", alphabet = alphabet):
    case Some(idx): expect idx == 63
    case nil: expect false
```

</details>

#### returns nil for not found

- returns nil for not found


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns nil for not found")
val alphabet = base64_alphabet()
match find_base64_index(c = "@", alphabet = alphabet):
    case Some(_): expect false
    case nil: expect true
```

</details>

### Encoding

#### encodes single char with padding

- encodes single char with padding


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("encodes single char with padding")
val result = encode_base64("A")
expect result.len() > 0
expect result.contains("=")
```

</details>

#### encodes two chars with one padding

- encodes two chars with one padding


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("encodes two chars with one padding")
val result = encode_base64("AB")
expect result.len() == 4
expect result.ends_with("=")
```

</details>

#### encodes three chars without padding

- encodes three chars without padding


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("encodes three chars without padding")
val result = encode_base64("ABC")
expect result.len() == 4
expect not result.contains("=")
```

</details>

#### encodes empty string

- encodes empty string


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("encodes empty string")
expect encode_base64("") == ""
```

</details>

### Decoding

#### decodes valid base64

- decodes valid base64


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("decodes valid base64")
val encoded = encode_base64("ABC")
match decode_base64(encoded):
    case Some(decoded): expect decoded == "ABC"
    case nil: expect false
```

</details>

#### decodes with padding

- decodes with padding


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("decodes with padding")
val encoded = encode_base64("AB")
match decode_base64(encoded):
    case Some(decoded): expect decoded == "AB"
    case nil: expect false
```

</details>

#### decodes empty string

- decodes empty string


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("decodes empty string")
match decode_base64(""):
    case Some(decoded): expect decoded == ""
    case nil: expect false
```

</details>

#### returns nil for invalid chars

- returns nil for invalid chars


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns nil for invalid chars")
match decode_base64("@#$%"):
    case Some(_): expect false
    case nil: expect true
```

</details>

#### returns nil for incomplete input

- returns nil for incomplete input


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns nil for incomplete input")
match decode_base64("A"):
    case Some(_): expect false
    case nil: expect true
```

</details>

### URL-Safe Encoding

#### encodes without + / =

- encodes without + / =


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("encodes without + / =")
val result = encode_base64_url("ABC")
expect not result.contains("+")
expect not result.contains("/")
expect not result.contains("=")
```

</details>

#### decodes url-safe encoding

- decodes url-safe encoding


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("decodes url-safe encoding")
val original = "ABC"
val encoded = encode_base64_url(original)
match decode_base64_url(encoded):
    case Some(decoded): expect decoded == original
    case nil: expect false
```

</details>

### Validation

#### validates simple base64

- validates simple base64


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("validates simple base64")
expect is_valid_base64("ABCD")
```

</details>

#### validates with padding

- validates with padding


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("validates with padding")
expect is_valid_base64("AB==")
```

</details>

#### validates with numbers

- validates with numbers


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("validates with numbers")
expect is_valid_base64("ABC123")
```

</details>

#### validates with special chars

- validates with special chars


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("validates with special chars")
expect is_valid_base64("AB+/")
```

</details>

#### validates empty string

- validates empty string


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("validates empty string")
expect is_valid_base64("")
```

</details>

#### rejects invalid chars

- rejects invalid chars


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rejects invalid chars")
expect not is_valid_base64("ABC@")
```

</details>

#### rejects too much padding

- rejects too much padding


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rejects too much padding")
expect not is_valid_base64("A===")
```

</details>

### Round-trip

#### encodes and decodes single char

- encodes and decodes single char


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("encodes and decodes single char")
val original = "A"
val encoded = encode_base64(original)
match decode_base64(encoded):
    case Some(decoded): expect decoded == original
    case nil: expect false
```

</details>

#### encodes and decodes three chars

- encodes and decodes three chars


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("encodes and decodes three chars")
val original = "ABC"
val encoded = encode_base64(original)
match decode_base64(encoded):
    case Some(decoded): expect decoded == original
    case nil: expect false
```

</details>

#### encodes and decodes lowercase

- encodes and decodes lowercase


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("encodes and decodes lowercase")
val original = "abc"
val encoded = encode_base64(original)
match decode_base64(encoded):
    case Some(decoded): expect decoded == original
    case nil: expect false
```

</details>

#### encodes and decodes digits

- encodes and decodes digits


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("encodes and decodes digits")
val original = "012"
val encoded = encode_base64(original)
match decode_base64(encoded):
    case Some(decoded): expect decoded == original
    case nil: expect false
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/unit/app/tooling/base64_utils_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering Base64 Utilities, Alphabet, Character Conversion, Find Index, Encoding, Decoding, URL-Safe Encoding, Validation, Round-trip.
- Base64 Utilities
- Alphabet
- Character Conversion
- Find Index
- Encoding
- Decoding
- URL-Safe Encoding
- Validation
- Round-trip

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 35 |
| Active scenarios | 35 |
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

- Canonical SPipe generation for source `27d35724981d791c1d1d1a017607156a55c476f8bee642cdb85ae3868f0d2bff`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `27d35724981d791c1d1d1a017607156a55c476f8bee642cdb85ae3868f0d2bff`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `27d35724981d791c1d1d1a017607156a55c476f8bee642cdb85ae3868f0d2bff`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/unit/app/tooling/base64_utils_spec.spl
mirror: doc/06_spec/unit/app/tooling/base64_utils_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/unit/app/tooling/base64_utils_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/unit/app/tooling/base64_utils_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/unit/app/tooling/base64_utils_spec.spl:115:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'has 64 characters' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/app/tooling/base64_utils_spec.spl:121:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'starts with ABC' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/app/tooling/base64_utils_spec.spl:127:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'ends with +/' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
