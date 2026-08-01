# Base64 Utils Specification

> 1. expect alphabet len

<!-- sdn-diagram:id=base64_utils_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=base64_utils_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

base64_utils_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=base64_utils_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

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

1. expect alphabet len


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val alphabet = base64_alphabet()
expect alphabet.len() == 64
```

</details>

#### starts with ABC

1. expect alphabet starts with


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val alphabet = base64_alphabet()
expect alphabet.starts_with("ABC")
```

</details>

#### ends with +/

1. expect alphabet ends with


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val alphabet = base64_alphabet()
expect alphabet.ends_with("+/")
```

</details>

### Character Conversion

#### converts letters to bytes

1. expect char to byte
2. expect char to byte
3. expect char to byte
4. expect char to byte


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect char_to_byte("A") == 65
expect char_to_byte("B") == 66
expect char_to_byte("a") == 97
expect char_to_byte("b") == 98
```

</details>

#### converts digits to bytes

1. expect char to byte
2. expect char to byte
3. expect char to byte


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect char_to_byte("0") == 48
expect char_to_byte("1") == 49
expect char_to_byte("2") == 50
```

</details>

#### converts special chars to bytes

1. expect char to byte
2. expect char to byte


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect char_to_byte(" ") == 32
expect char_to_byte("!") == 33
```

</details>

#### converts bytes to letters

1. expect byte to char
2. expect byte to char
3. expect byte to char


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect byte_to_char(65) == "A"
expect byte_to_char(66) == "B"
expect byte_to_char(97) == "a"
```

</details>

#### converts bytes to digits

1. expect byte to char
2. expect byte to char


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect byte_to_char(48) == "0"
expect byte_to_char(49) == "1"
```

</details>

#### returns ? for unknown bytes

1. expect byte to char


<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect byte_to_char(255) == "?"
```

</details>

### Find Index

#### finds A at index 0

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val alphabet = base64_alphabet()
match find_base64_index(c = "A", alphabet = alphabet):
    case Some(idx): expect idx == 0
    case nil: expect false
```

</details>

#### finds a at index 26

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val alphabet = base64_alphabet()
match find_base64_index(c = "a", alphabet = alphabet):
    case Some(idx): expect idx == 26
    case nil: expect false
```

</details>

#### finds / at index 63

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val alphabet = base64_alphabet()
match find_base64_index(c = "/", alphabet = alphabet):
    case Some(idx): expect idx == 63
    case nil: expect false
```

</details>

#### returns nil for not found

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val alphabet = base64_alphabet()
match find_base64_index(c = "@", alphabet = alphabet):
    case Some(_): expect false
    case nil: expect true
```

</details>

### Encoding

#### encodes single char with padding

1. expect result len
2. expect result contains


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = encode_base64("A")
expect result.len() > 0
expect result.contains("=")
```

</details>

#### encodes two chars with one padding

1. expect result len
2. expect result ends with


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = encode_base64("AB")
expect result.len() == 4
expect result.ends_with("=")
```

</details>

#### encodes three chars without padding

1. expect result len
2. expect not result contains


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = encode_base64("ABC")
expect result.len() == 4
expect not result.contains("=")
```

</details>

#### encodes empty string

1. expect encode base64


<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect encode_base64("") == ""
```

</details>

### Decoding

#### decodes valid base64

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val encoded = encode_base64("ABC")
match decode_base64(encoded):
    case Some(decoded): expect decoded == "ABC"
    case nil: expect false
```

</details>

#### decodes with padding

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val encoded = encode_base64("AB")
match decode_base64(encoded):
    case Some(decoded): expect decoded == "AB"
    case nil: expect false
```

</details>

#### decodes empty string

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
match decode_base64(""):
    case Some(decoded): expect decoded == ""
    case nil: expect false
```

</details>

#### returns nil for invalid chars

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
match decode_base64("@#$%"):
    case Some(_): expect false
    case nil: expect true
```

</details>

#### returns nil for incomplete input

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
match decode_base64("A"):
    case Some(_): expect false
    case nil: expect true
```

</details>

### URL-Safe Encoding

#### encodes without + / =

1. expect not result contains
2. expect not result contains
3. expect not result contains


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = encode_base64_url("ABC")
expect not result.contains("+")
expect not result.contains("/")
expect not result.contains("=")
```

</details>

#### decodes url-safe encoding

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val original = "ABC"
val encoded = encode_base64_url(original)
match decode_base64_url(encoded):
    case Some(decoded): expect decoded == original
    case nil: expect false
```

</details>

### Validation

#### validates simple base64

1. expect is valid base64


<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect is_valid_base64("ABCD")
```

</details>

#### validates with padding

1. expect is valid base64


<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect is_valid_base64("AB==")
```

</details>

#### validates with numbers

1. expect is valid base64


<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect is_valid_base64("ABC123")
```

</details>

#### validates with special chars

1. expect is valid base64


<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect is_valid_base64("AB+/")
```

</details>

#### validates empty string

1. expect is valid base64


<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect is_valid_base64("")
```

</details>

#### rejects invalid chars

1. expect not is valid base64


<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect not is_valid_base64("ABC@")
```

</details>

#### rejects too much padding

1. expect not is valid base64


<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect not is_valid_base64("A===")
```

</details>

### Round-trip

#### encodes and decodes single char

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val original = "A"
val encoded = encode_base64(original)
match decode_base64(encoded):
    case Some(decoded): expect decoded == original
    case nil: expect false
```

</details>

#### encodes and decodes three chars

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val original = "ABC"
val encoded = encode_base64(original)
match decode_base64(encoded):
    case Some(decoded): expect decoded == original
    case nil: expect false
```

</details>

#### encodes and decodes lowercase

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val original = "abc"
val encoded = encode_base64(original)
match decode_base64(encoded):
    case Some(decoded): expect decoded == original
    case nil: expect false
```

</details>

#### encodes and decodes digits

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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
| Source | `test/01_unit/app/tooling/base64_utils_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
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
