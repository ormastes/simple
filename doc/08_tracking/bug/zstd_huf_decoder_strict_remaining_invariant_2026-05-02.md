# Zstd HUF decoder strict `remaining != 0` invariant — incompatible with mixed-length encoder

**Status:** RESOLVED (W14-A, 2026-05-02) — see Resolution section below. Original framing falsified by W13-B; encoder-side root cause fixed.
**Severity:** blocks RFC-8478 compliant Zstd Huffman literal encoder from round-tripping through the existing pure-Simple decoder.
**Path:** `bug` track. Decoder-side fix; W9-C encoder primitives are dead-on-shelf until this lands.

## Symptom

W9-C landed Zstd Huffman literal encoder primitives (`zstd_huf_encode_literals`) that pass structural unit tests but FAIL discriminating round-trip through the existing pure-Simple decoder `_zstd_decode_huffman_stream`.

W12-E disproved the W9-C "bit-direction mismatch" framing (Brotli-precedent analogy). End-to-end trace:
- Decoder fills `slot = reverse(code,bits) | (suffix << bits)` in `zstd_huf_expand_decode_table`
- Encoder emits `reverse(code,bits)` LSB-first via `zstd_bit_writer_append_lsb`
- Compositions match. Bit-direction is consistent.

## Root cause (one of two, this is the HUF half)

`src/lib/common/compress/zstd.spl:896` — `_zstd_decode_huffman_stream` enforces:

```spl
if zstd_bits_remaining(reader) != 0 { return Err(...) }
```

at end-of-stream. Combined with the windowed `peek(table_bits) ; consume(entry.bits)` decoding loop, this strict invariant is **mathematically incompatible** with any RFC-8478 Huffman encoder for mixed-length alphabets (i.e., where different symbols have different code lengths):

- **Pre-padding** (low-reservoir position, decoded-LAST): the trailing pad bits leak into the strict `remaining == 0` check at end-of-stream. The decoder reads the actual data correctly, then errors on pad-bit residue.
- **Post-padding** (high-reservoir position, decoded-FIRST): the `peek(table_bits)` of the first iteration reads window-bits that include pad bits, corrupting the first decoded codeword.

There is **no encoder-only fix**. Any encoder that produces a valid HUF stream per RFC 8478 will trip one of these two failure modes given the current decoder.

## Strict-check provenance

Added by commit `88b3b82722`. Predates W9-C work. The strict check appears to be over-conservative beyond what RFC 8478 §4.2.1 mandates — the spec says streams end on a 1-bit terminator, but the decoder's exact byte-position check goes further.

## Affected encoders

- **W9-C `zstd_huf_encode_literals`** (`src/lib/common/compress/zstd_huf.spl`) — deferred from end-to-end test for this reason.
- Any future RFC-8478-compliant Huffman literal encoder.

## Affected decoded streams (currently passing)

The decoder works correctly for streams that happen to end with no pad bits — most reference test vectors crafted for the existing pure-Simple decoder path. Production zstd output uses encoders that produce pad bits (per RFC 8478 §4.2.1), so this is a real interop gap.

## Fix

Replace strict `remaining != 0` check with RFC 8478 §4.2.1 sentinel-bit termination logic:

1. Decoder reads up to but not past the 1-bit terminator marker.
2. End-of-stream condition: pad-byte ends with `1` followed by zero or more `0`s — count the trailing zeros + leading 1 bit, and consider the stream consumed at that point.
3. Allow the consumed-bit count to exceed exact byte boundary as long as the terminator was honored.

Reference: RFC 8478 §4.2.1.5 "Huffman-Coded Streams"; the four-stream variant uses a 1-bit-then-zeros padding to align to byte boundary.

## Verification

After fix:
- Round-trip W9-C `zstd_huf_encode_literals` output through `_zstd_decode_huffman_stream` byte-exact.
- Cross-check against `zstd` CLI output (commit a small fixture per `scripts/`)
- Existing decoder specs continue to PASS (no regression).

## Out of scope

- The orthogonal FSE encoder bug at `zstd_fse.spl:415` (filed separately at `bug_zstd_huf_literal_encoder_bit_layout_2026-05-02.md` § revised hypothesis).
- W9-C façade level relax {3}→{1,2,3} — verified by W12-E to NOT route through this encoder, no regression.

## Cross-references

- `doc/08_tracking/bug/bug_zstd_huf_literal_encoder_bit_layout_2026-05-02.md` § revised hypothesis (W12-E investigation).
- W12-E commit `7a2d261b50c1` doc(zstd): revise W9-C bug-doc hypothesis after end-to-end trace.
- W9-C commits at `d7e46403c2`, `a248ebff0a`, `0dcf6c357c`, `afad9a3907`, `9516e68fa7`, `1e98028811`.
- `src/lib/common/compress/zstd.spl:896` (strict check).
- `src/lib/common/compress/zstd_huf.spl` (encoder primitives).
- RFC 8478 §4.2.1.5.

## Revised hypothesis (W13-B, 2026-05-02)

The original framing in this doc — that the strict `remaining != 0` check at
`zstd.spl:896` is mathematically incompatible with RFC-8478-compliant
mixed-length Huffman encoders, and that the fix is to relax the check using
sentinel-bit termination — is **wrong**. This section disproves it
empirically and redirects ownership to the encoder side.

### Falsifying evidence

W13-B wrote a probe spec
(`test/unit/lib/common/zstd_huf_round_trip_probe_spec.spl`, since removed)
that ran `zstd_huf_encode_literals` -> `zstd_huf_decode_stream_for_test` for
three inputs:

1. Uniform 8-symbol input -> **fails at ENCODE**, not decode
   (`_zstd_huf_assign_weights` weight-balancing rejection — separate issue,
   out of scope here).
2. Skewed input (`a*8 b*4 c*2 d*1`, mixed-length codes) -> decode reaches
   end of literal loop, then errors with
   `zstd Huffman literal stream has trailing bits`.
3. Highly skewed input (`A*16 B*4 C*2 D*1`) -> same failure mode.

The decoder loop completes the full `regenerated_size` literals (i.e. it
DOES decode the right number of symbols) before the strict check fires.

W13-B then temporarily disabled the strict check and re-ran the probe with
byte-by-byte comparison of `decoded` vs input:

- Input 2: `byte[8] got=97 want=98` — first ~8 literals (the `a` run) decode
  correctly, but the `b` run is decoded as `a`s.
- Input 3: `byte[16] got=65 want=66` — first 16 literals (the `A` run)
  decode correctly, but the `B` run is decoded as `A`s.

So the literals are CORRUPTED, not just trailing-bit padding. The strict
check is correctly reporting a real corruption.

### Why the original framing fails

`zstd_bits_init` already implements RFC 8478 §4.2.1.5 sentinel-bit
termination:

```
val tail = data[end - 1]
val valid_bits = _zstd_highbit_index(tail)
val reservoir = tail.to_u64() & _zstd_low_bits_mask(valid_bits)
```

This locates the high-bit-1 sentinel and masks both the sentinel AND the
zero pad bits above it out of the reservoir. After init, the reservoir +
remaining bytes hold exactly N data bits, where N = total bits emitted by
the encoder before `zstd_bit_writer_finish` appended the sentinel.

If the decoder consumes `sum_of(entry.bits)` during the literal loop and
`zstd_bits_remaining(reader) != 0` at the end, the only possible
interpretation is: **encoder emitted more bits per symbol than the decoder
consumed for those symbols**. The strict check is correctly flagging this.

The original "pre-pad bits leak" / "post-pad bits corrupt first peek"
mechanism does not exist — the sentinel and pad zeros never reach the
reservoir.

### Real bug location (encoder side)

Per the falsifying probe (corrupted literals, not just trailing pad), the
defect is one or both of:

- **Encoder per-symbol bit-count mismatch:** the `(bits, code)` pair that
  `zstd_huf_encoder_lookup` extracts from `zstd_huf_build_canonical_entries`
  uses different bit lengths than the decode table built by
  `_zstd_huf_build_table_from_weights` for the same weights.
- **Encoder code-value mismatch:** the canonical code value emitted (after
  `zstd_huf_reverse_bits`) does not produce the table index that maps to
  the originally-input symbol.

Reproduction: build canonical entries from a known weight set, build the
decode table from the same weights, then check that for every symbol s,
`decode_table[reverse_bits(canonical[s].code, canonical[s].bits)].symbol
== s` and `.bits == canonical[s].bits`. Any mismatch is the bug.

### Disposition

- The decoder-side fix prescribed in this doc (relax `remaining != 0`,
  add sentinel-bit termination logic) is **rejected**. Implementing it
  would silently accept the encoder's corrupted output —
  `feedback_no_coverups.md` violation.
- Strict check at `zstd.spl:896` stays as-is.
- Ownership transfers to encoder track. Follow-up: fix the per-symbol
  encoder/decoder agreement in `zstd_huf.spl` (`zstd_huf_encode_literals`
  / `zstd_huf_build_canonical_entries` / `_zstd_huf_encoder_lookup` vs
  `_zstd_huf_build_table_from_weights` / `zstd_huf_expand_decode_table`).
- Empirical probe artefact: see W13-B commit message; spec was
  intentionally not landed because it would add 3 failing tests to CI
  before the encoder fix.

## Resolution (W14-A, 2026-05-02)

**Status: RESOLVED.** Encoder fix landed in `src/lib/common/compress/zstd_huf.spl`.
Round-trip spec at `test/unit/lib/common/zstd_huf_round_trip_spec.spl` — 3/3 PASS
including W13-B's falsifying inputs `a*8 b*4 c*2 d*1` and `A*16 B*4 C*2 D*1`.

### W13-B's redirection was right; specific probe was wrong

W14-A diagnosed the actual root cause: **byte-stream layout layer**, not per-symbol
`(bits, code)` table disagreement. The W13-B prescribed probe (build canonical
entries, build decode table from same weights, assert
`decode_table[reverse_bits(canonical[s].code, canonical[s].bits)].symbol == s`)
would have **passed** — the per-symbol agreement IS correct. The defect only
manifests for multi-byte streams.

Mechanism: the W9-C encoder used `zstd_bit_writer_append_lsb` + reverse-literal
emit order. After the decoder's `ZstdBackwardBits` reader does init+full-refill,
it reads the byte buffer in scrambled order: `data[end-1]` LSBs (after marker
strip), then `data[end-2]` LSB-to-MSB, ..., `data[start]` LSB-to-MSB. Encoder
emissions span byte boundaries; the byte-reversed-LSB-within-byte read jumps
stream position non-monotonically. This corrupts everything past the first
byte.

### Fix

- Drop `zstd_bit_writer_*` from this stream entirely.
- Emit literals in **input order** (lit[0] first) into a flat LSB-first bit
  buffer (`byte_buf` + `leftover` reservoir).
- At finish, **repack** into the layout the decoder expects:
  `out[end-1] = bits[0..V-1] | (1 << V)` (marker byte, V = K mod 8);
  `out[end-2-j]` = bits `V+8j..V+8j+7` packed LSB-first. Output bytes pushed in
  reverse so `out[end-1]` lands last.
- Each output byte straddles two `byte_buf` entries because `V` shifts the byte
  boundary.

### Decoder unchanged

Strict `remaining != 0` invariant at `zstd.spl:896` — **untouched**. The
round-trip spec relies on it firing 0. W13-B's analysis that this check is
correctly catching real corruption was right.

### Commits

W14-A work landed across (jj auto-snapshot scattered, mis-titled per
`feedback_jj_uncommitted_clobbered_by_parallel.md`):
- `5a4a819959` — encoder body + doc comment
- `ac9de24e84` — encoder import removal
- `47dc92e3d0` + `975f53d1f0` — round-trip spec
- `3360b06811` — final test refinement

### Lessons

- W13-B's bug-doc redirection ("encoder side, not decoder") was correct.
- W13-B's specific probe instructions (per-symbol `(bits, code)` agreement
  check) would have produced a false-clear — the per-symbol mapping was
  already right. The byte-stream layout layer is invisible to that probe.
- Updated mental model: when a decoder uses a non-monotonic byte-order
  read (here: `end-1` LSBs, then `end-2` LSB-to-MSB, ...), encoders MUST
  emit in the matching layout, not in stream order with an LSB-first bit
  writer.
