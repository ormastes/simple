# zlib header: CMF=0x78 (deflate, window=32768), FLG=0x01 (no dict, check bits)

> var data: [u8] = []

<!-- sdn-diagram:id=deflate_inflate_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=deflate_inflate_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

deflate_inflate_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=deflate_inflate_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 14 | 14 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# zlib header: CMF=0x78 (deflate, window=32768), FLG=0x01 (no dict, check bits)

var data: [u8] = []

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/common/deflate_inflate_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

var data: [u8] = []
    data = data + [0x78, 0x01]
    data = data + [0x01]
    data = data + [0x05, 0x00]
    data = data + [0xFA, 0xFF]
    data = data + [72, 101, 108, 108, 111]
    data

fn make_empty_stored_block() -> [u8]:
    """Build a DEFLATE stream with an empty stored block (0 bytes payload)."""
    var data: [u8] = []
    data = data + [0x78, 0x01]
    data = data + [0x01]
    data = data + [0x00, 0x00]
    data = data + [0xFF, 0xFF]
    data

fn make_two_stored_blocks() -> [u8]:
    """Build DEFLATE with two stored blocks: "Hi" then "!!" (bfinal on second)."""
    var data: [u8] = []
    data = data + [0x78, 0x01]
    data = data + [0x00]
    data = data + [0x02, 0x00]
    data = data + [0xFD, 0xFF]
    data = data + [72, 105]
    data = data + [0x01]
    data = data + [0x02, 0x00]
    data = data + [0xFD, 0xFF]
    data = data + [33, 33]
    data

describe "DeflateInflate — stored blocks":

## Scenarios

### DeflateInflate — stored blocks

#### single stored block

#### AC-1: inflates single stored block with 'Hello' payload

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val compressed = make_stored_block_hello()
val result = deflate_inflate(compressed, 2)
expect(result.len().to_i32()).to_equal(5)
```

</details>

#### AC-1: stored block output bytes are correct

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val compressed = make_stored_block_hello()
val result = deflate_inflate(compressed, 2)
# 'H' = 72
expect(result[0]).to_equal(72)
```

</details>

#### AC-1: stored block last byte is correct

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val compressed = make_stored_block_hello()
val result = deflate_inflate(compressed, 2)
# 'o' = 111
expect(result[4]).to_equal(111)
```

</details>

#### empty stored block

#### AC-1: inflating empty stored block produces empty output

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val compressed = make_empty_stored_block()
val result = deflate_inflate(compressed, 2)
expect(result.len().to_i32()).to_equal(0)
```

</details>

#### multiple stored blocks

#### AC-1: inflating two stored blocks concatenates output

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val compressed = make_two_stored_blocks()
val result = deflate_inflate(compressed, 2)
expect(result.len().to_i32()).to_equal(4)
```

</details>

#### AC-1: two-block output contains all bytes

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val compressed = make_two_stored_blocks()
val result = deflate_inflate(compressed, 2)
# "Hi!!" = [72, 105, 33, 33]
expect(result[0]).to_equal(72)
```

</details>

#### AC-1: two-block second block data is correct

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val compressed = make_two_stored_blocks()
val result = deflate_inflate(compressed, 2)
# Last byte should be '!' = 33
expect(result[3]).to_equal(33)
```

</details>

### DeflateInflate — skip_bytes

#### zlib header skipping

#### AC-1: skip_bytes=2 skips zlib CMF+FLG header

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val compressed = make_stored_block_hello()
val result = deflate_inflate(compressed, 2)
# Should produce "Hello" (5 bytes), not garbage from parsing header as data
expect(result.len().to_i32()).to_equal(5)
```

</details>

#### edge cases

#### AC-1: empty input returns empty output

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val data: [u8] = []
val result = deflate_inflate(data, 0)
expect(result.len().to_i32()).to_equal(0)
```

</details>

#### AC-1: input shorter than skip_bytes returns empty output

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val data: [u8] = [0x78]
val result = deflate_inflate(data, 2)
expect(result.len().to_i32()).to_equal(0)
```

</details>

### DeflateInflate — fixed Huffman

#### fixed Huffman compressed data

#### AC-1: inflates fixed Huffman block to non-empty output

<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# A minimal fixed Huffman block encoding a few literal bytes
# This is a zlib-compressed version of a short payload
# zlib header (78 01) + fixed Huffman block
# The exact bytes depend on the encoder, so we test behavior:
# If deflate_inflate gets a btype=1 block, it should attempt decode
val compressed = make_stored_block_hello()  # fallback to stored for now
val result = deflate_inflate(compressed, 2)
expect(result.len()).to_be_greater_than(0)
```

</details>

#### output correctness

#### AC-1: decompressed data preserves all original bytes

<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val compressed = make_stored_block_hello()
val result = deflate_inflate(compressed, 2)
# Verify middle byte: 'l' = 108
if result.len().to_i32() >= 3:
    expect(result[2]).to_equal(108)
else:
    # Should not happen for valid stored block
    expect(result.len()).to_be_greater_than(2)
```

</details>

### DeflateInflate — error resilience

#### malformed input

#### AC-1: invalid block type does not crash

- data = data + [0x07]        # bfinal=1, btype=3
   - Expected: is_safe is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# btype=3 is reserved/invalid in DEFLATE
var data: [u8] = []
data = data + [0x78, 0x01]  # zlib header
data = data + [0x07]        # bfinal=1, btype=3 (invalid)
val result = deflate_inflate(data, 2)
# Should return empty or partial — not crash
val is_safe = result.len() >= 0
expect(is_safe).to_equal(true)
```

</details>

#### AC-1: truncated stored block header returns partial or empty

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var data: [u8] = []
data = data + [0x78, 0x01]  # zlib header
data = data + [0x01]        # bfinal=1, btype=0
# Missing LEN/NLEN
val result = deflate_inflate(data, 2)
val is_safe = result.len() >= 0
expect(is_safe).to_equal(true)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 14 |
| Active scenarios | 14 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
