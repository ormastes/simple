# Bencode Specification

> Tests covering Bencode integer encode, Bencode integer decode, Bencode integer round-trip, Bencode string encode, Bencode string decode, Bencode string round-trip, Bencode list encode, Bencode list round-trip, Bencode bytes encode, Bencode dict encode, Bencode dict round-trip, Bencode simple decode API, Bencode torrent-style metadata.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 42 | 42 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Bencode Specification

## Scenarios

### Bencode integer encode

#### encodes 42 as i42e

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- encodes 42 as i42e
   - Expected: _enc_int_42() equals `i42e`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("encodes 42 as i42e")
expect(_enc_int_42()).to_equal("i42e")
```

</details>

#### encodes 0 as i0e

- encodes 0 as i0e
   - Expected: _enc_int_zero() equals `i0e`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("encodes 0 as i0e")
expect(_enc_int_zero()).to_equal("i0e")
```

</details>

#### encodes -3 as i-3e

- encodes -3 as i-3e
   - Expected: _enc_int_neg3() equals `i-3e`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("encodes -3 as i-3e")
expect(_enc_int_neg3()).to_equal("i-3e")
```

</details>

#### encodes large positive integer

- encodes large positive integer
   - Expected: _enc_int_large() equals `i1000000e`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("encodes large positive integer")
expect(_enc_int_large()).to_equal("i1000000e")
```

</details>

### Bencode integer decode

#### decodes i42e to 42 at new_pos 4

- decodes i42e to 42 at new_pos 4
   - Expected: r[0] equals `42`
   - Expected: r[1] equals `4`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("decodes i42e to 42 at new_pos 4")
val r = _dec_int_42()
expect(r[0]).to_equal("42")
expect(r[1]).to_equal("4")
```

</details>

#### decodes i0e to 0

- decodes i0e to 0
   - Expected: r[0] equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("decodes i0e to 0")
val r = _dec_int_zero()
expect(r[0]).to_equal("0")
```

</details>

#### decodes i-3e to -3

- decodes i-3e to -3
   - Expected: r[0] equals `-3`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("decodes i-3e to -3")
val r = _dec_int_neg3()
expect(r[0]).to_equal("-3")
```

</details>

#### rejects i-0e (negative zero)

- rejects i-0e (negative zero)
   - Expected: _dec_int_neg_zero_is_error() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rejects i-0e (negative zero)")
expect(_dec_int_neg_zero_is_error()).to_equal(true)
```

</details>

#### rejects i03e (leading zero)

- rejects i03e (leading zero)
   - Expected: _dec_int_leading_zero_is_error() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rejects i03e (leading zero)")
expect(_dec_int_leading_zero_is_error()).to_equal(true)
```

</details>

#### decodes integer at offset in larger string

- decodes integer at offset in larger string
   - Expected: r[0] equals `42`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("decodes integer at offset in larger string")
val r = _dec_int_pos_at_offset()
expect(r[0]).to_equal("42")
```

</details>

#### decodes i64::MIN (-9223372036854775808), the boundary negative value

- decodes i64::MIN (-9223372036854775808), the boundary negative value
   - Expected: r[0] equals `-9223372036854775808`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("decodes i64::MIN (-9223372036854775808), the boundary negative value")
val r = _dec_int_i64_min()
expect(r[0]).to_equal("-9223372036854775808")
```

</details>

### Bencode integer round-trip

#### 42 round-trips

- 42 round-trips
   - Expected: _rt_int_42() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("42 round-trips")
expect(_rt_int_42()).to_equal(true)
```

</details>

#### 0 round-trips

- 0 round-trips
   - Expected: _rt_int_zero() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("0 round-trips")
expect(_rt_int_zero()).to_equal(true)
```

</details>

#### -3 round-trips

- -3 round-trips
   - Expected: _rt_int_neg3() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("-3 round-trips")
expect(_rt_int_neg3()).to_equal(true)
```

</details>

#### large positive integer round-trips

- large positive integer round-trips
   - Expected: _rt_int_large() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("large positive integer round-trips")
expect(_rt_int_large()).to_equal(true)
```

</details>

### Bencode string encode

#### encodes 'spam' as 4:spam

- encodes 'spam' as 4:spam
   - Expected: _enc_str_spam() equals `4:spam`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("encodes 'spam' as 4:spam")
expect(_enc_str_spam()).to_equal("4:spam")
```

</details>

#### encodes empty string as 0:

- encodes empty string as 0:
   - Expected: _enc_str_empty() equals `0:`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("encodes empty string as 0:")
expect(_enc_str_empty()).to_equal("0:")
```

</details>

#### encodes 'egg' as 3:egg

- encodes 'egg' as 3:egg
   - Expected: _enc_str_egg() equals `3:egg`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("encodes 'egg' as 3:egg")
expect(_enc_str_egg()).to_equal("3:egg")
```

</details>

#### encodes 'hello world' with correct length prefix

- encodes 'hello world' with correct length prefix
   - Expected: _enc_str_hello() equals `11:hello world`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("encodes 'hello world' with correct length prefix")
expect(_enc_str_hello()).to_equal("11:hello world")
```

</details>

### Bencode string decode

#### decodes 4:spam to 'spam' at new_pos 6

- decodes 4:spam to 'spam' at new_pos 6
   - Expected: r[0] equals `spam`
   - Expected: r[1] equals `6`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("decodes 4:spam to 'spam' at new_pos 6")
val r = _dec_str_spam()
expect(r[0]).to_equal("spam")
expect(r[1]).to_equal("6")
```

</details>

#### decodes 0: to empty string

- decodes 0: to empty string
   - Expected: r[0] equals ``
   - Expected: r[1] equals `2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("decodes 0: to empty string")
val r = _dec_str_empty()
expect(r[0]).to_equal("")
expect(r[1]).to_equal("2")
```

</details>

#### decodes string at offset in larger string

- decodes string at offset in larger string
   - Expected: r[0] equals `spam`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("decodes string at offset in larger string")
val r = _dec_str_at_offset()
expect(r[0]).to_equal("spam")
```

</details>

### Bencode string round-trip

#### 'spam' round-trips

- 'spam' round-trips
   - Expected: _rt_str_spam() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("'spam' round-trips")
expect(_rt_str_spam()).to_equal(true)
```

</details>

#### empty string round-trips

- empty string round-trips
   - Expected: _rt_str_empty() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("empty string round-trips")
expect(_rt_str_empty()).to_equal(true)
```

</details>

#### 'hello world' round-trips

- 'hello world' round-trips
   - Expected: _rt_str_hello() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("'hello world' round-trips")
expect(_rt_str_hello()).to_equal(true)
```

</details>

### Bencode list encode

#### encodes [spam, 42] as l4:spami42ee

- encodes [spam, 42] as l4:spami42ee
   - Expected: _enc_list_simple() equals `l4:spami42ee`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("encodes [spam, 42] as l4:spami42ee")
expect(_enc_list_simple()).to_equal("l4:spami42ee")
```

</details>

#### encodes empty list as le

- encodes empty list as le
   - Expected: _enc_list_empty() equals `le`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("encodes empty list as le")
expect(_enc_list_empty()).to_equal("le")
```

</details>

#### encodes nested list correctly

- encodes nested list correctly
   - Expected: _enc_list_nested() equals `l4:spamli42eee`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("encodes nested list correctly")
expect(_enc_list_nested()).to_equal("l4:spamli42eee")
```

</details>

### Bencode list round-trip

#### simple list [spam, 42] round-trips

- simple list [spam, 42] round-trips
   - Expected: _rt_list_simple() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("simple list [spam, 42] round-trips")
expect(_rt_list_simple()).to_equal(true)
```

</details>

#### nested list round-trips

- nested list round-trips
   - Expected: _rt_nested_list() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("nested list round-trips")
expect(_rt_nested_list()).to_equal(true)
```

</details>

### Bencode bytes encode

#### encodes [u8] bytes with length prefix

- encodes [u8] bytes with length prefix
   - Expected: _enc_bytes_check() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("encodes [u8] bytes with length prefix")
expect(_enc_bytes_check()).to_equal(true)
```

</details>

### Bencode dict encode

#### encodes empty dict as de

- encodes empty dict as de
   - Expected: _enc_dict_empty() equals `de`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("encodes empty dict as de")
expect(_enc_dict_empty()).to_equal("de")
```

</details>

#### encodes single-entry dict correctly

- encodes single-entry dict correctly
   - Expected: _enc_dict_single() equals `d3:keyi1ee`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("encodes single-entry dict correctly")
expect(_enc_dict_single()).to_equal("d3:keyi1ee")
```

</details>

#### encodes dict with keys sorted lexicographically

- encodes dict with keys sorted lexicographically
   - Expected: _enc_dict_simple() equals `d3:cow3:moo4:spam4:eggse`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("encodes dict with keys sorted lexicographically")
# cow < spam, so cow:moo comes before spam:eggs
expect(_enc_dict_simple()).to_equal("d3:cow3:moo4:spam4:eggse")
```

</details>

### Bencode dict round-trip

#### dict with keys in order round-trips

- dict with keys in order round-trips
   - Expected: _rt_dict_sorted() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("dict with keys in order round-trips")
expect(_rt_dict_sorted()).to_equal(true)
```

</details>

### Bencode simple decode API

#### bencode_decode parses integer

- bencode_decode parses integer
   - Expected: _simple_decode_int() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("bencode_decode parses integer")
expect(_simple_decode_int()).to_equal(true)
```

</details>

#### bencode_decode parses string

- bencode_decode parses string
   - Expected: _simple_decode_str() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("bencode_decode parses string")
expect(_simple_decode_str()).to_equal(true)
```

</details>

#### bencode_decode parses list — returns item count

- bencode_decode parses list — returns item count
   - Expected: _simple_decode_list() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("bencode_decode parses list — returns item count")
expect(_simple_decode_list()).to_equal(true)
```

</details>

#### bencode_decode parses dict — returns entry count

- bencode_decode parses dict — returns entry count
   - Expected: _simple_decode_dict() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("bencode_decode parses dict — returns entry count")
expect(_simple_decode_dict()).to_equal(true)
```

</details>

#### bencode_decode rejects trailing data

- bencode_decode rejects trailing data
   - Expected: _simple_decode_trailing_error() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("bencode_decode rejects trailing data")
expect(_simple_decode_trailing_error()).to_equal(true)
```

</details>

### Bencode torrent-style metadata

#### info dict round-trips with 3 keys

- info dict round-trips with 3 keys
   - Expected: _torrent_info_dict_roundtrip() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("info dict round-trips with 3 keys")
expect(_torrent_info_dict_roundtrip()).to_equal(true)
```

</details>

#### full metainfo dict round-trips with 2 top-level keys

- full metainfo dict round-trips with 2 top-level keys
   - Expected: _torrent_metainfo() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("full metainfo dict round-trips with 2 top-level keys")
expect(_torrent_metainfo()).to_equal(true)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/unit/lib/common/encoding/bencode_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering Bencode integer encode, Bencode integer decode, Bencode integer round-trip, Bencode string encode, Bencode string decode, Bencode string round-trip, Bencode list encode, Bencode list round-trip, Bencode bytes encode, Bencode dict encode, Bencode dict round-trip, Bencode simple decode API, Bencode torrent-style metadata.
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
| Total scenarios | 42 |
| Active scenarios | 42 |
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

- Canonical SPipe generation for source `f2dfc09312bc28752cf2ff3cbe33cf644bd4c45cbcf2ddc64f85bc607f5e15af`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `f2dfc09312bc28752cf2ff3cbe33cf644bd4c45cbcf2ddc64f85bc607f5e15af`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `f2dfc09312bc28752cf2ff3cbe33cf644bd4c45cbcf2ddc64f85bc607f5e15af`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/unit/lib/common/encoding/bencode_spec.spl
mirror: doc/06_spec/unit/lib/common/encoding/bencode_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/unit/lib/common/encoding/bencode_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/unit/lib/common/encoding/bencode_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/unit/lib/common/encoding/bencode_spec.spl:325:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'encodes 42 as i42e' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/lib/common/encoding/bencode_spec.spl:330:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'encodes 0 as i0e' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/lib/common/encoding/bencode_spec.spl:335:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'encodes -3 as i-3e' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
