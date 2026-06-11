# Zstd Dictionary Specification

> <details>

<!-- sdn-diagram:id=zstd_dictionary_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=zstd_dictionary_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

zstd_dictionary_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=zstd_dictionary_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 10 | 10 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Zstd Dictionary Specification

## Scenarios

### zstd dictionary-frame decode (RFC 8478 §6)

#### parses a well-formed dictionary blob and seeds entropy state

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(MODULE_PARSE_OK.is_ok()).to_equal(true)
val state = MODULE_PARSE_OK.unwrap()
expect(state.repeat_offsets.rep1).to_equal(1)
expect(state.repeat_offsets.rep2).to_equal(4)
expect(state.repeat_offsets.rep3).to_equal(8)
expect(state.content_prefix.len()).to_equal(16)
expect(state.huffman.is_some()).to_equal(true)
```

</details>

#### rejects a dictionary with a wrong Magic_Number

1.  expect compression error


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(MODULE_PARSE_BAD_MAGIC.is_err()).to_equal(true)
_expect_compression_error(MODULE_PARSE_BAD_MAGIC.unwrap_err(), "InvalidHeader", "dictionary magic")
```

</details>

#### rejects a Dictionary_ID mismatch

1.  expect compression error


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(MODULE_PARSE_BAD_ID.is_err()).to_equal(true)
_expect_compression_error(MODULE_PARSE_BAD_ID.unwrap_err(), "CorruptStream", "dictionary id mismatch")
```

</details>

#### rejects a dictionary truncated after the Huffman section

1.  expect compression error


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(MODULE_PARSE_TRUNC.is_err()).to_equal(true)
_expect_compression_error(MODULE_PARSE_TRUNC.unwrap_err(), "TruncatedInput", "FSE")
```

</details>

#### rejects a dictionary truncated mid recommended offsets

1.  expect compression error


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(MODULE_PARSE_TRUNC_REPS.is_err()).to_equal(true)
_expect_compression_error(MODULE_PARSE_TRUNC_REPS.unwrap_err(), "TruncatedInput", "recommended offsets")
```

</details>

#### rejects a dictionary with a zero recommended offset

1.  expect compression error


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(MODULE_PARSE_ZERO_REP.is_err()).to_equal(true)
_expect_compression_error(MODULE_PARSE_ZERO_REP.unwrap_err(), "CorruptStream", "recommended offset")
```

</details>

#### decodes a Raw_Block frame referencing the dictionary by id

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(MODULE_DECODE_FRAME.is_ok()).to_equal(true)
val out = MODULE_DECODE_FRAME.unwrap()
expect(out.len()).to_equal(12)
# "HELLO_DICT!!" - 0x48 0x45 0x4C 0x4C 0x4F 0x5F 0x44 0x49 0x43 0x54 0x21 0x21
expect(out[0]).to_equal(0x48u8)
expect(out[5]).to_equal(0x5Fu8)
expect(out[10]).to_equal(0x21u8)
```

</details>

#### rejects a dict-referencing frame when no dictionary is supplied

1.  expect compression error


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(MODULE_DECODE_FRAME_NO_DICT.is_err()).to_equal(true)
_expect_compression_error(MODULE_DECODE_FRAME_NO_DICT.unwrap_err(), "UnsupportedFeature", "dictionary-backed frames require")
```

</details>

#### consumes seeded Huffman state via a Treeless_Literals_Block (end-to-end)

<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# AC-1: dictionary-supplied huffman_table_state is the only way the
# Treeless block here can decode. If `_zstd_frame_dictionary_state`
# didn't actually flow `dictionary_state.huffman` into the frame's
# huffman_table_state slot, the literals dispatch would fail with
# `UnsupportedFeature("treeless literals need a prior Huffman table")`.
expect(MODULE_DECODE_TREELESS_WITH_DICT.is_ok()).to_equal(true)
val out = MODULE_DECODE_TREELESS_WITH_DICT.unwrap()
expect(out.len()).to_equal(4)
expect(out[0]).to_equal(0x00u8)
expect(out[1]).to_equal(0x00u8)
expect(out[2]).to_equal(0x00u8)
expect(out[3]).to_equal(0x02u8)
```

</details>

#### rejects Treeless literals when no dictionary state seeds Huffman (typed error)

1.  expect compression error


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# AC-2: same Compressed_Block payload but the frame's FHD declares
# DID_flag=0, so no dictionary state seeds huffman_table_state. The
# decoder MUST fail with the precise typed error rather than emit
# silent garbage bytes.
expect(MODULE_DECODE_TREELESS_NO_DICT.is_err()).to_equal(true)
_expect_compression_error(MODULE_DECODE_TREELESS_NO_DICT.unwrap_err(), "UnsupportedFeature", "treeless literals")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/common/zstd_dictionary_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- zstd dictionary-frame decode (RFC 8478 §6)

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 10 |
| Active scenarios | 10 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
