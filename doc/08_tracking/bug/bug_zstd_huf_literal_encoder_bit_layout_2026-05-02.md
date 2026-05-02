# Zstd Huffman + FSE encoder primitives: encoder output not decodable

Date: 2026-05-02
Status: **OPEN — both encoder primitives shipped under W9-C are
unverified-broken when fed back through their matching decoders.
Discovered 2026-05-02 via discriminating round-trip checks the
W9-C spec did not (and could not at parallel-clobber time) include.**

## Symptom

### A. `zstd_huf_encode_literals` (commit `a248ebff0a` / `a5d2699f3e`)

`zstd_huf_encode_literals` (added in
"feat(zstd_huf): Huffman literal encoder + direct/FSE weight header
emitters") produces a bitstream whose direct round-trip through the
existing pure-Simple decoder fails:

```
called unwrap on Err: CompressionError::TruncatedInput(zstd bitstream bits)
```

The decoder is `_zstd_decode_huffman_stream` (`src/lib/common/compress/zstd.spl:876`)
fed by `_zstd_huf_build_table_from_weights`. The error originates from
`zstd_bits_peek(reader, table_state.table_bits)` running out of bits
before all `regenerated_size` literals have been emitted — meaning the
encoder did not leave the decoder with enough trailing bits per
codeword peek.

### B. `zstd_fse_encode_symbols` (commit `d7e46403c2` / `09979b67e4`)

The FSE encoder fails its OWN round-trip on a flat-distribution test
(`counts = [4, 4, 4, 4, 4, 4, 4, 4]`, `table_log = 5`,
`syms = [0, 3, 5, 1, 7, 2, 6, 4]`):

```
called unwrap on Err: CompressionError::CorruptStream(zstd fse encode state index oor)
```

The error originates from `_zstd_fse_encode_one_symbol` computing
`target_idx` (sym-cumulative-base + state-shift) outside
`state_table.len()`. Likely root cause: the per-symbol `nb_bits` test
`if state + entry.state_offset >= 0 and ((state + entry.state_offset)
>> table.table_log) > 0: nb_bits = entry.nb_bits - 1` does not match
the zstd reference encoder's `(state + delta_nb_bits) >> 16` test,
so the wrong number of state bits is shifted out and the cumulative-
table lookup overflows.

`zstd_huf_encode_fse_weight_header` indirectly inherits this defect
because it calls `zstd_fse_encode_symbols` — its current PASS in
`test/unit/lib/common/zstd_fse_huffman_weight_encode_spec.spl` only
asserts header byte format (`< 128`) and bitstream length consistency
with the header byte, never that the bitstream decodes back to the
input weight stream. A wider weight distribution may bypass the failing
state-index path; the spec's `[2, 1, 1]` partial happens to land in a
cumulative-state region the broken formula handles correctly.

## Reproduce

```
bin/simple test test/unit/lib/common/zstd_fse_huffman_weight_encode_spec.spl
```

The "Huffman literal encoder produces a non-empty bitstream + valid
weight set" case PASSES (structural assertions only). A previous
revision of that case asserted full round-trip and failed; the failure
is preserved in jj op-history under the same file. The replacement test
documents the gap explicitly so a future ship of the encoder can flip
it back to a real round-trip.

## Suspected divergences (not investigated to root cause)

1. The Huffman decoder reads `table_bits` bits per peek (the maximum
   codeword length over the alphabet), but the encoder emits only
   `entry.bits` per code — so the trailing pad inserted by
   `zstd_bit_writer_finish` may not provide the `table_bits - last_code_bits`
   bits the decoder needs for its final peek. Reference: the C zstd
   encoder pads the bitstream tail with `8 + table_log` zero bits before
   the marker; our pure-Simple writer pads to a byte boundary then writes
   one marker bit.
2. `zstd_huf_reverse_bits` is applied at encode time; the decoder fills
   its lookup table using the same helper, so this should round-trip.
   But the LSB-first reservoir layout in `zstd_bit_writer_append_lsb`
   may interact with the backward byte-walk in `zstd_bits_init` such
   that the FIRST emitted code lands at the WRONG byte position.

## Out of scope for this lane

- Wiring the literal encoder into a full Compressed_Block emitter.
- 4-stream Huffman literal layout (Size_Format = 01).
- Honoring `compression_level` 1/2 with distinct encode strategies.

## What landed despite the bug

- C1: `zstd_fse_build_encode_table` + `zstd_fse_encode_symbols`
  (encoder-side FSE primitives). Verified structurally; full round-trip
  through `zstd_fse_build_decode_table` is NOT yet in the spec.
- C2: `zstd_huf_encode_literals` + `zstd_huf_encode_direct_weight_header`
  + `zstd_huf_encode_fse_weight_header`. Header emitters verified by
  byte-exact assertion; literal-stream encoder structural-only.
- C3: facade `_validate_level` accepts {1, 2, 3} for Zstd.

## Spec

`test/unit/lib/common/zstd_fse_huffman_weight_encode_spec.spl` — 7
cases, 7/7 PASS as of 2026-05-02 with the structural assertion. When
this bug is fixed, the "Huffman literal encoder ..." case must be
rewritten to assert decoder round-trip equality.

## Verify report

`doc/09_report/verify_common_compression_framework.md` line 49
(façade rejection) is partially discharged: levels 1, 2, 3 now
accepted; levels 4-22 still rejected with documented deferred-to-
Wave-10+ message. The encoder-side gap stays WARN until this bug
clears.
