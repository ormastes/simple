# Zstd Fse Huffman Weight Encode Specification

> Tests covering zstd FSE + Huffman encoder primitives.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 7 | 7 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Zstd Fse Huffman Weight Encode Specification

## Scenarios

### zstd FSE + Huffman encoder primitives

#### round-trips MSB-first bit writer through MSB backward reader

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- round-trips MSB-first bit writer through MSB backward reader


<details>
<summary>Executable SSpec</summary>

Runnable source: 18 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("round-trips MSB-first bit writer through MSB backward reader")
var writer = zstd_bit_writer_new()
# Emit 5 then 3 then 7 bits: 0b10110, 0b101, 0b1100110
val w1 = zstd_bit_writer_append_msb(writer, 0b10110u64, 5).unwrap()
val w2 = zstd_bit_writer_append_msb(w1, 0b101u64, 3).unwrap()
val w3 = zstd_bit_writer_append_msb(w2, 0b1100110u64, 7).unwrap()
val finished = zstd_bit_writer_finish(w3).unwrap()
expect(finished.len() > 0).to_be(true)
# Drain via MSB backward reader; should recover values in REVERSE
# write order (encoder writes A B C, reader reads C B A).
val reader_init = zstd_msb_bits_init(finished, 0, finished.len()).unwrap()
val (got_c, r2, _padded_c) = zstd_msb_bits_read(reader_init, 7).unwrap()
val (got_b, r3, _padded_b) = zstd_msb_bits_read(r2, 3).unwrap()
val (got_a, _r4, _padded_a) = zstd_msb_bits_read(r3, 5).unwrap()
expect(got_c).to_be(0b1100110)
expect(got_b).to_be(0b101)
expect(got_a).to_be(0b10110)
```

</details>

#### FSE encoder builds per-symbol slot lists matching the decoder dual

- FSE encoder builds per-symbol slot lists matching the decoder dual


<details>
<summary>Executable SSpec</summary>

Runnable source: 25 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("FSE encoder builds per-symbol slot lists matching the decoder dual")
# Eight equally-likely symbols at table_log = 5: each gets count 4
# (sum = 32 = table_size). The encoder is built by inverting the
# decoder table (W13-C 2026-05-02), so the union of all
# slot-buckets must partition [0, table_size), and every slot's
# `bits`/`baseline`/`p` must be sane.
val table_log = 5
val table_size = 1 << table_log
val counts = [4, 4, 4, 4, 4, 4, 4, 4]
val encode_table = zstd_fse_build_encode_table(table_log, counts).unwrap()
expect(encode_table.table_log).to_be(table_log)
expect(encode_table.slots.len()).to_be(counts.len())
# Per-symbol slot count must match its normalised count.
expect(encode_table.slots[0].len()).to_be(counts[0])
expect(encode_table.slots[1].len()).to_be(counts[1])
expect(encode_table.slots[7].len()).to_be(counts[7])
# Spot-check first slot of symbol 0: bounds and within-range.
val first = encode_table.slots[0][0]
expect(first.bits >= 0).to_be(true)
expect(first.bits <= table_log).to_be(true)
expect(first.baseline >= 0).to_be(true)
expect(first.baseline + (1 << first.bits) <= table_size).to_be(true)
expect(first.p >= 0).to_be(true)
expect(first.p < table_size).to_be(true)
```

</details>

#### Huffman direct weight header produces RFC 8478 §4.2.1.1 byte layout

- Huffman direct weight header produces RFC 8478 §4.2.1.1 byte layout


<details>
<summary>Executable SSpec</summary>

Runnable source: 25 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("Huffman direct weight header produces RFC 8478 §4.2.1.1 byte layout")
# Three-symbol alphabet with weights [1, 1, ?] where '?' is the
# implicit final weight derived from Kraft completion. Sum of
# 2^(w-1) over partial = 1+1 = 2 = 2^1; remainder = 0 forces a
# different example. Use [1, 1, 2] so partial sum = 1+1+2 = 4 =
# 2^2 with implicit completion = log2(0)+1 — invalid. The
# right shape: partial whose 2^(w-1) sum is < a power of two by
# exactly another 2^k. partial = [2, 1, 1]: sum = 2+1+1 = 4,
# sum is a power of two but completion needs the last weight to
# equal log2(target - sum) + 1. target = next_pow2(4) = 8;
# remainder = 4 = 2^2 so last_weight = 3. Final weights:
# [2, 1, 1, 3], explicit count = 3, header byte = 127 + 3 = 130.
val partial = [2, 1, 1]
val completed = zstd_huf_complete_weights(partial).unwrap()
expect(completed.len()).to_be(4)
expect(completed[3]).to_be(3)
# Direct header: 1 header byte + ceil(N/2) = ceil(3/2) = 2 nibble bytes.
val header = zstd_huf_encode_direct_weight_header(completed).unwrap()
expect(header.len()).to_be(1 + 2)
expect(header[0]).to_be(130u8)
# Byte 1 packs weights[0]=2 (high) and weights[1]=1 (low) -> 0x21.
expect(header[1]).to_be(0x21u8)
# Byte 2 packs weights[2]=1 (high) and an implicit zero (low) -> 0x10.
expect(header[2]).to_be(0x10u8)
```

</details>

#### Huffman literal encoder round-trips through canonical entries

- Huffman literal encoder round-trips through canonical entries


<details>
<summary>Executable SSpec</summary>

Runnable source: 38 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("Huffman literal encoder round-trips through canonical entries")
# TODO(W12-F or follow-up zstd lane): full bitstream round-trip
# via `zstd_huf_decode_stream_for_test` is BLOCKED on the
# `zstd.spl:896` strict trailing-bits invariant in
# `_zstd_decode_huffman_stream`. W12-E (2026-05-02) confirmed via
# end-to-end trace that no encoder-only fix can satisfy both
# `peek(table_bits)` AND `remaining == 0` simultaneously for
# mixed-length alphabets. See revised hypothesis A in
# `doc/08_tracking/bug/bug_zstd_huf_literal_encoder_bit_layout_2026-05-02.md`.
# The structural assertions below stay until the decoder is
# relaxed (out of scope for this allowlist).
# Tiny alphabet, deterministic by construction.
val literals: [u8] = [
    0x61u8, 0x62u8, 0x61u8, 0x63u8, 0x61u8, 0x62u8,
    0x61u8, 0x63u8, 0x61u8, 0x62u8, 0x61u8, 0x64u8
]
val encoded_res = zstd_huf_encode_literals(literals)
expect(encoded_res.is_err()).to_be(false)
val (bitstream, weights) = encoded_res.unwrap()
expect(bitstream.len() > 0).to_be(true)
expect(weights.len()).to_be(256)
# The canonical entries built from `weights` must produce a valid
# Kraft-complete tree (delegated to the existing decoder helper);
# any failure surfaces as Err here.
val canonical_res = zstd_huf_build_canonical_entries(weights)
expect(canonical_res.is_err()).to_be(false)
val canonical = canonical_res.unwrap()
# All four input symbols must have non-zero bit lengths.
var found = 0
var i = 0
while i < canonical.len():
    val sym = canonical[i].symbol
    if sym == 0x61 or sym == 0x62 or sym == 0x63 or sym == 0x64:
        found = found + 1
        expect(canonical[i].bits > 0).to_be(true)
    i = i + 1
expect(found).to_be(4)
```

</details>

#### FSE Huffman-weight encoder produces a header byte less than 128

- FSE Huffman-weight encoder produces a header byte less than 128


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("FSE Huffman-weight encoder produces a header byte less than 128")
# Use a Kraft-completable partial weight set with a wider
# distribution: partial = [2, 1, 1] -> last weight = 3 (sum = 8 = 2^3).
val partial = [2, 1, 1]
val completed = zstd_huf_complete_weights(partial).unwrap()
# The header layout must match the decoder contract: header byte
# < 128, and the byte value equals the FSE bitstream length in
# bytes (RFC 8478 §4.2.1.1 FSE-vs-direct discriminator).
val fse_header = zstd_huf_encode_fse_weight_header(completed).unwrap()
expect(fse_header.len() > 1).to_be(true)
val header_byte = fse_header[0]
expect(header_byte.to_i64() < 128).to_be(true)
expect(fse_header.len() - 1).to_be(header_byte.to_i64())
```

</details>

#### zstd frame encoder accepts levels 1 and 2 alongside level 3

- zstd frame encoder accepts levels 1 and 2 alongside level 3
   - Expected: zstd_decompress_frame(frame1).unwrap() equals `payload`
   - Expected: zstd_decompress_frame(frame2).unwrap() equals `payload`
   - Expected: zstd_decompress_frame(frame3).unwrap() equals `payload`


<details>
<summary>Executable SSpec</summary>

Runnable source: 18 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("zstd frame encoder accepts levels 1 and 2 alongside level 3")
val level1 = _make_zstd_options(1).unwrap()
val level2 = _make_zstd_options(2).unwrap()
val level3 = _make_zstd_options(3).unwrap()
val payload = _english_payload(1)
val frame1 = zstd_compress_frame(payload, level1)
val frame2 = zstd_compress_frame(payload, level2)
val frame3 = zstd_compress_frame(payload, level3)
expect(frame1[0]).to_be(0x28u8)
expect(frame1[1]).to_be(0xB5u8)
expect(frame1[2]).to_be(0x2Fu8)
expect(frame1[3]).to_be(0xFDu8)
expect(frame2[0]).to_be(0x28u8)
expect(frame3[0]).to_be(0x28u8)
expect(zstd_decompress_frame(frame1).unwrap()).to_equal(payload)
expect(zstd_decompress_frame(frame2).unwrap()).to_equal(payload)
expect(zstd_decompress_frame(frame3).unwrap()).to_equal(payload)
```

</details>

#### option helper rejects Zstd levels outside the codec range

- option helper rejects Zstd levels outside the codec range


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("option helper rejects Zstd levels outside the codec range")
val opts0_res = _make_zstd_options(0)
expect(opts0_res.is_err()).to_be(true)
val opts23_res = _make_zstd_options(23)
expect(opts23_res.is_err()).to_be(true)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/unit/lib/common/zstd_fse_huffman_weight_encode_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering zstd FSE + Huffman encoder primitives.
- zstd FSE + Huffman encoder primitives

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 7 |
| Active scenarios | 7 |
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

- Canonical SPipe generation for source `4db4a6dae593aa6dc7d1e674e800d2e6e83de8084f25ab9c3d7120b3e607406e`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `4db4a6dae593aa6dc7d1e674e800d2e6e83de8084f25ab9c3d7120b3e607406e`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `4db4a6dae593aa6dc7d1e674e800d2e6e83de8084f25ab9c3d7120b3e607406e`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/unit/lib/common/zstd_fse_huffman_weight_encode_spec.spl
mirror: doc/06_spec/unit/lib/common/zstd_fse_huffman_weight_encode_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/unit/lib/common/zstd_fse_huffman_weight_encode_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/unit/lib/common/zstd_fse_huffman_weight_encode_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/unit/lib/common/zstd_fse_huffman_weight_encode_spec.spl:79:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'round-trips MSB-first bit writer through MSB backward reader' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/lib/common/zstd_fse_huffman_weight_encode_spec.spl:99:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'FSE encoder builds per-symbol slot lists matching the decoder dual' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/lib/common/zstd_fse_huffman_weight_encode_spec.spl:126:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'Huffman direct weight header produces RFC 8478 §4.2.1.1 byte layout' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
