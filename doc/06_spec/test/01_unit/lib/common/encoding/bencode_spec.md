# Bencode Specification

> <details>

<!-- sdn-diagram:id=bencode_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=bencode_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

bencode_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=bencode_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 41 | 41 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Bencode Specification

## Scenarios

### Bencode integer encode

#### encodes 42 as i42e

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_enc_int_42()).to_equal("i42e")
```

</details>

#### encodes 0 as i0e

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_enc_int_zero()).to_equal("i0e")
```

</details>

#### encodes -3 as i-3e

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_enc_int_neg3()).to_equal("i-3e")
```

</details>

#### encodes large positive integer

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_enc_int_large()).to_equal("i1000000e")
```

</details>

### Bencode integer decode

#### decodes i42e to 42 at new_pos 4

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val r = _dec_int_42()
expect(r[0]).to_equal("42")
expect(r[1]).to_equal("4")
```

</details>

#### decodes i0e to 0

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val r = _dec_int_zero()
expect(r[0]).to_equal("0")
```

</details>

#### decodes i-3e to -3

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val r = _dec_int_neg3()
expect(r[0]).to_equal("-3")
```

</details>

#### rejects i-0e (negative zero)

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_dec_int_neg_zero_is_error()).to_equal(true)
```

</details>

#### rejects i03e (leading zero)

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_dec_int_leading_zero_is_error()).to_equal(true)
```

</details>

#### decodes integer at offset in larger string

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val r = _dec_int_pos_at_offset()
expect(r[0]).to_equal("42")
```

</details>

### Bencode integer round-trip

#### 42 round-trips

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_rt_int_42()).to_equal(true)
```

</details>

#### 0 round-trips

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_rt_int_zero()).to_equal(true)
```

</details>

#### -3 round-trips

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_rt_int_neg3()).to_equal(true)
```

</details>

#### large positive integer round-trips

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_rt_int_large()).to_equal(true)
```

</details>

### Bencode string encode

#### encodes 'spam' as 4:spam

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_enc_str_spam()).to_equal("4:spam")
```

</details>

#### encodes empty string as 0:

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_enc_str_empty()).to_equal("0:")
```

</details>

#### encodes 'egg' as 3:egg

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_enc_str_egg()).to_equal("3:egg")
```

</details>

#### encodes 'hello world' with correct length prefix

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_enc_str_hello()).to_equal("11:hello world")
```

</details>

### Bencode string decode

#### decodes 4:spam to 'spam' at new_pos 6

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val r = _dec_str_spam()
expect(r[0]).to_equal("spam")
expect(r[1]).to_equal("6")
```

</details>

#### decodes 0: to empty string

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val r = _dec_str_empty()
expect(r[0]).to_equal("")
expect(r[1]).to_equal("2")
```

</details>

#### decodes string at offset in larger string

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val r = _dec_str_at_offset()
expect(r[0]).to_equal("spam")
```

</details>

### Bencode string round-trip

#### 'spam' round-trips

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_rt_str_spam()).to_equal(true)
```

</details>

#### empty string round-trips

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_rt_str_empty()).to_equal(true)
```

</details>

#### 'hello world' round-trips

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_rt_str_hello()).to_equal(true)
```

</details>

### Bencode list encode

#### encodes [spam, 42] as l4:spami42ee

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_enc_list_simple()).to_equal("l4:spami42ee")
```

</details>

#### encodes empty list as le

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_enc_list_empty()).to_equal("le")
```

</details>

#### encodes nested list correctly

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_enc_list_nested()).to_equal("l4:spamli42eee")
```

</details>

### Bencode list round-trip

#### simple list [spam, 42] round-trips

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_rt_list_simple()).to_equal(true)
```

</details>

#### nested list round-trips

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_rt_nested_list()).to_equal(true)
```

</details>

### Bencode bytes encode

#### encodes [u8] bytes with length prefix

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_enc_bytes_check()).to_equal(true)
```

</details>

### Bencode dict encode

#### encodes empty dict as de

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_enc_dict_empty()).to_equal("de")
```

</details>

#### encodes single-entry dict correctly

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_enc_dict_single()).to_equal("d3:keyi1ee")
```

</details>

#### encodes dict with keys sorted lexicographically

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# cow < spam, so cow:moo comes before spam:eggs
expect(_enc_dict_simple()).to_equal("d3:cow3:moo4:spam4:eggse")
```

</details>

### Bencode dict round-trip

#### dict with keys in order round-trips

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_rt_dict_sorted()).to_equal(true)
```

</details>

### Bencode simple decode API

#### bencode_decode parses integer

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_simple_decode_int()).to_equal(true)
```

</details>

#### bencode_decode parses string

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_simple_decode_str()).to_equal(true)
```

</details>

#### bencode_decode parses list — returns item count

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_simple_decode_list()).to_equal(true)
```

</details>

#### bencode_decode parses dict — returns entry count

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_simple_decode_dict()).to_equal(true)
```

</details>

#### bencode_decode rejects trailing data

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_simple_decode_trailing_error()).to_equal(true)
```

</details>

### Bencode torrent-style metadata

#### info dict round-trips with 3 keys

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_torrent_info_dict_roundtrip()).to_equal(true)
```

</details>

#### full metainfo dict round-trips with 2 top-level keys

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_torrent_metainfo()).to_equal(true)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/common/encoding/bencode_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- Bencode integer encode
- Bencode integer decode
- Bencode integer round-trip
- Bencode string encode
- Bencode string decode
- Bencode string round-trip
- Bencode list encode
- Bencode list round-trip
- Bencode bytes encode
- Bencode dict encode
- Bencode dict round-trip
- Bencode simple decode API
- Bencode torrent-style metadata

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 41 |
| Active scenarios | 41 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
