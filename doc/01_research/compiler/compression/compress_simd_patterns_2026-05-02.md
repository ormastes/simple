# Compression SIMD Opportunity Audit — 2026-05-02

**Scope:** Pure read-only audit of `src/lib/` compression implementations.
**Goal:** Identify SIMD-vectorisable hot loops, rank them, and record file:line citations for every claim.
**Out of scope:** vendored third-party code, runtime FFI internals (SIMD opportunity for those is in `src/runtime/`), other Wave J lanes.

---

## §1 Overview

### 1.1 Algorithms present

| Algorithm | Primary file(s) | Implementation language | Layer |
|-----------|----------------|------------------------|-------|
| zstd (FSE/ANS, Huffman, LZ77, dict) | `src/lib/common/compress/zstd.spl`, `zstd_fse.spl`, `zstd_huf.spl`, `zstd_bits.spl` | Pure Simple | common |
| gzip / DEFLATE (Huffman, LZ77, sliding window) | `src/lib/nogc_sync_mut/compression/gzip/` (8 submodules), `gzip_utils.spl` | Pure Simple | nogc_sync_mut |
| LZ4 (hash table, 4-byte hash, match copy) | `src/lib/common/compress/lz4.spl`, `nogc_sync_mut/compression/lz4.spl` | Pure Simple | common + nogc |
| LZMA2 / XZ | `src/lib/common/compress/lzma2.spl` | Pure Simple | common |
| Brotli (RFC 7932) | `src/lib/nogc_sync_mut/compression/brotli/` (decoder.spl, encoder.spl, bit_reader.spl, bit_writer.spl) | Pure Simple | nogc_sync_mut |
| General Huffman (canonical) | `src/lib/common/huffman/` (6 files) | Pure Simple | common |
| HPACK Huffman (HTTP/2, RFC 7541) | `src/lib/common/hpack/huffman_h2.spl` | Pure Simple | common |
| LZ77 primitives (shared) | `src/lib/common/lz77/` (compress.spl, decompress.spl, match.spl, mod.spl, types.spl) | Pure Simple | common |
| Compression utilities (CRC32, xxHash32/64, tier detection) | `src/lib/common/compress/utilities.spl` | Pure Simple | common |
| gzip FFI facade | `src/lib/nogc_sync_mut/io/compress_ffi.spl` | FFI extern | nogc_sync_mut |
| UPX wrapper | `src/lib/nogc_sync_mut/compress/upx.spl` | FFI extern | nogc_sync_mut |

**Absent:** standalone brotli in `common/`, standalone DEFLATE-only library; no raw LZO, snappy, or zlib found.

### 1.2 FFI vs. Pure-Simple boundary

`src/lib/nogc_sync_mut/io/compress_ffi.spl:13-21` declares:

```
extern fn rt_gzip_compress(data: text, level: i64) -> text
extern fn rt_gzip_decompress(data: text) -> text
extern fn rt_deflate_compress(data: text, level: i64) -> text
extern fn rt_deflate_decompress(data: text) -> text
```

These six externs delegate entirely to the Rust seed runtime. **SIMD opportunity for these is in `src/runtime/`, not in the Simple wrapper.** All sections below address only the pure-Simple implementations.

### 1.3 Existing SIMD scaffolding

`src/lib/common/compress/utilities.spl:1-29` already defines:

```
enum CompressionSimdTier: scalar | avx2 | neon
fn compression_simd_tier_detect() -> CompressionSimdTier
```

`_for_tier` variants exist for CRC32 (`utilities.spl:191`), xxhash32 (`utilities.spl:247`), and xxhash64 (`zstd.spl` ~`1108`). However, **every inner loop is still scalar** — the tier branches merely set `chunk_width` but then execute `_crc32_update_byte` (a per-byte update) per lane. The xxhash32 chunk path (`utilities.spl:230`) reads four u32 lanes sequentially. The xxhash64 tier branch (`zstd.spl:1125`) hardcodes `chunk_width = 32` regardless of AVX2 vs. NEON (bug: `if avx2: 32 else: 32`). The framework is in place; the intrinsics are not yet wired.

### 1.4 Open bug context

Three open bugs are relevant to SIMD prioritisation:

- `doc/08_tracking/bug/bug_zstd_huf_literal_encoder_bit_layout_2026-05-02.md` — FSE encoder output not decodable; encoder-side hot loops are partially broken.
- `doc/08_tracking/bug/bug_zstd_fse_encoder_nb_bits_formula_2026-05-02.md` — FSE nb_bits formula wrong.
- `doc/08_tracking/bug/bug_zstd_fse_huffman_weight_kraft_2026-05-01.md` — Huffman weight decode incorrect on real fixtures.

**Do not prioritise SIMD on the encoder side until these bugs are fixed.**

---

## §2 zstd

### 2.1 Location

| File | Purpose |
|------|---------|
| `src/lib/common/compress/zstd.spl` | Top-level decoder: frame header, literals section, sequences section, block loop, dictionary, xxHash64 checksum |
| `src/lib/common/compress/zstd_fse.spl` | FSE/ANS: normalised counts, decode-table build, encode-table build, symbol encode |
| `src/lib/common/compress/zstd_huf.spl` | Huffman: canonical entries, 4-stream Huffman weight decode |
| `src/lib/common/compress/zstd_bits.spl` | Bit readers: `ZstdBackwardBits` (LSB-first, backward), `ZstdMsbBackwardBits` |

### 2.2 Hot-loop pattern A — Huffman literal decode [DECOMPRESS]

**File:line:** `src/lib/common/compress/zstd.spl:884`

```
while literals.len() < regenerated_size:
    val idx_res = zstd_bits_peek(reader, table_state.table_bits)
    val entry = table_state.table[idx_res.unwrap().to_i64()]
    literals.push(entry.symbol.to_u8())
    val next_res = zstd_bits_consume(reader, entry.bits)
    reader = next_res.unwrap()
```

Pattern: table-lookup decode — peek `table_bits` bits, index into a flat decode table, emit symbol, consume bits. Runs once per output byte.

**SIMD opportunity:** zstd uses a 4-stream Huffman layout (`_zstd_decode_huffman_4streams`, `zstd.spl:919`). The four calls to `_zstd_decode_huffman_stream` are currently **serial**. Each stream is independent and could run concurrently. On AVX2, 4 independent streams can maintain 4 in-flight bit-cursor state vectors, updating all four with SIMD gathers and table lookups per group of 4 symbols. Expected throughput improvement: ~3-4× for literal-heavy blocks (main bottleneck in decompression of text/source data). Reference: Yann Collet, "Finite State Entropy" (2013 blog) documents that 4-way interleaving hides decode-table latency on out-of-order CPUs.

**Existing language:** Pure Simple.
**Expected speedup:** 3–4× for literal-heavy payloads (4-stream parallel decode).
**Difficulty:** HARD (requires coordinating four independent bit-stream states).

### 2.3 Hot-loop pattern B — FSE sequence decode [DECOMPRESS]

**File:line:** `src/lib/common/compress/zstd.spl:504` (outer sequence loop), and inside
`_zstd_decode_fse_sequences` at `zstd.spl:478`.

The sequence decode loop processes `sequence_count` triples (literal_length, match_length, offset) via three interleaved FSE states. Each iteration:
1. Reads `zstd_fse_get_entry` from offset/litlen/matchlen tables.
2. Reads extra bits via `zstd_bits_read`.
3. Advances each FSE state.

**File:line (state advance):** `src/lib/common/compress/zstd_fse.spl:231` (the spread-table scan loop) and `zstd_fse.spl:248` (build decode table inner loop).

**SIMD opportunity:** Batching `nb_bits` reads for several sequences at once using SIMD bit-extraction. Intel's PDEP/PEXT or ARM NEON shift-and-mask can deinterleave bit fields from a packed 64-bit word for multiple sequences simultaneously. Realistic gain: 1.5–2× on sequence decode throughput. This is incremental because the sequences themselves have data dependencies (repeat offsets).

**Existing language:** Pure Simple.
**Expected speedup:** 1.5–2× (PDEP/PEXT batch bit extraction).
**Difficulty:** HARD (state machine dependencies; partial vectorisation only).

### 2.4 Hot-loop pattern C — sequence execution / match copy [DECOMPRESS]

**File:line:** `src/lib/common/compress/zstd.spl:669` (`_zstd_execute_sequences`), delegating to `src/lib/common/compress/utilities.spl:160` (`append_self_overlap_copy`).

```
fn append_self_overlap_copy(out: [u8], offset: i64, count: i64):
    while i < count:
        val src = result.len() - offset
        result.push(result[src])
        i = i + 1
```

Pattern: back-reference copy. If `offset >= count` (no overlap), this is a simple `memcpy`-like operation. If `offset < count`, it is RLE expansion (must stay scalar for the first `offset` bytes).

**SIMD opportunity:** Split into two cases:
- `offset >= 16` (AVX2) or `offset >= 8` (SSE2/NEON): use 16/32-byte SIMD copy, identical to a fast `memcpy` kernel.
- `offset < copy_len`: expand the first `offset` bytes as a repeating tile using SIMD broadcast/permute, then bulk copy the remainder.
This copy path is shared by both zstd (`zstd.spl:675`) and LZ4 (`lz4.spl:193`).

**Existing language:** Pure Simple.
**Expected speedup:** 4–8× for long matches (`offset >= 16`). For short or overlapping matches, gain is smaller. Reference: LZ4 project README documents that 8-byte SIMD wild-copy paths achieve ~3 GB/s on modern CPUs, vs ~1 GB/s for byte-by-byte.
**Difficulty:** MEDIUM (the large-offset case is a standard memcpy kernel; the overlap case is more careful).

### 2.5 Hot-loop pattern D — xxHash64 checksum [DECOMPRESS]

**File:line:** `src/lib/common/compress/zstd.spl:1125` (`_zstd_xxh64_bytes_for_tier`).

```
while idx + chunk_width <= data.len():
    val w1 = _zstd_read_u64_local(data, idx)
    ...
    v1 = _zstd_xxh64_round(v1, w1)
    v2 = _zstd_xxh64_round(v2, w2)
    v3 = _zstd_xxh64_round(v3, w3)
    v4 = _zstd_xxh64_round(v4, w4)
    idx = idx + chunk_width
```

**Note (bug):** `chunk_width` is hardcoded to 32 regardless of tier (`if avx2: 32 else: 32` at `zstd.spl:1126`). The NEON branch is dead code.

**SIMD opportunity:** On AVX2, load 256-bit chunks; compute four 64-bit accumulators with vmulq/vpaddq. `_zstd_read_u64_local` (`zstd.spl:1108`) uses an 8-byte manual unpack loop — replace with SIMD `_mm256_loadu_si256`.

**Existing language:** Pure Simple (with broken tier branch).
**Expected speedup:** 2–3× once u64 loads are SIMD-native (4 lanes simultaneously on AVX2).
**Difficulty:** MEDIUM (fix the tier branch first; then replace the u64 load loop).

---

## §3 gzip / DEFLATE

### 3.1 Location

All pure-Simple. Refactored from a monolithic `gzip_utils.spl` (originally 1,891 lines) into 8 submodules. The facade at `src/lib/nogc_sync_mut/gzip_utils.spl:1-46` re-exports everything.

| Submodule | File |
|-----------|------|
| Types / constants | `src/lib/nogc_sync_mut/compression/gzip/types.spl` |
| CRC32 | `src/lib/nogc_sync_mut/compression/gzip/crc.spl` |
| Header / footer | `src/lib/nogc_sync_mut/compression/gzip/header.spl` |
| LZ77 sliding window | `src/lib/nogc_sync_mut/compression/gzip/lz77.spl` (32 KB window, `MAX_DISTANCE`=32768) |
| Huffman | `src/lib/nogc_sync_mut/compression/gzip/huffman.spl` |
| DEFLATE blocks | `src/lib/nogc_sync_mut/compression/gzip/deflate.spl` |
| Inflate | `src/lib/nogc_sync_mut/compression/gzip/inflate.spl` |
| Stream | `src/lib/nogc_sync_mut/compression/gzip/stream.spl` |

Open bug: `doc/08_tracking/bug/gzip_module_crc32_unresolved_2026-05-01.md` — CRC32 symbol unresolved in some gzip paths.

### 3.2 Hot-loop pattern E — gzip Huffman frequency table build [COMPRESS]

**File:line:** `src/lib/nogc_sync_mut/compression/gzip/huffman.spl:47` (`huffman_freq_table`).

```
loop:
    val token = tokens[i]
    var found = false
    var j = 0
    loop:
        val entry = freqs[j]
        if sym == symbol:
            new_freqs.push([sym, count + 1])
            found = true
        ...
        j = j + 1
    i = i + 1
```

Pattern: frequency histogram built by linear scan of a dynamic list. O(n·m) where n = token count, m = alphabet size (up to 286 for lit/len, 30 for distance). The inner loop accesses `freqs[j]` — essentially a scatter-increment.

**SIMD opportunity:** Replace the linear-scan histogram with a fixed-length `[i64; 286]` array and use SIMD to scatter-increment 16 elements simultaneously (histogram via SIMD vpermd + vpaddq, or simple vectorised indexed add). Even without scatter intrinsics, a 256-entry `u8[286]` array with vectorised overflow check is 2–3× faster than list scan.

**Existing language:** Pure Simple (using dynamic list).
**Expected speedup:** 3–5× (from O(n·286) linear scan to O(n) array indexing + SIMD histogram).
**Difficulty:** MEDIUM (requires converting the dynamic-list histogram to a fixed array; no SIMD intrinsic needed for most of the gain).

### 3.3 Hot-loop pattern F — DEFLATE bitstream encode (token loop) [COMPRESS]

**File:line:** `src/lib/nogc_sync_mut/compression/gzip/deflate.spl:76` (`deflate_block_fixed`).

```
loop:
    val token = tokens[i]
    val token_type = token[0]
    val value = token[1]
    if token_type == 0:
        val code_info = huffman_lookup(lit_codes, value)
        bs = bitstream_write_huffman(bs, code_info[0], code_info[1])
    else:
        ...
    i = i + 1
```

Pattern: token-by-token Huffman encode with a lookup table. Bottleneck is `huffman_lookup` followed by bit-packing.

**SIMD opportunity:** Batch 8 or 16 literal tokens with a SIMD gather on a precomputed code/length table, then use SIMD bit-packing. Intel BitShuffle paper (2013) documents 3–4× over scalar for this pattern. However, the gzip Huffman encoder here uses dynamic Huffman trees rebuilt per block — vectorisation benefit is highest for the fixed-Huffman path.

**Existing language:** Pure Simple.
**Expected speedup:** 2–3× for fixed-Huffman path.
**Difficulty:** MEDIUM.

### 3.4 Hot-loop pattern G — CRC32 per-byte update [DECOMPRESS + COMPRESS]

**File:line:** `src/lib/common/compress/utilities.spl:171` (`_crc32_update_byte`) and `utilities.spl:191` (`crc32_bytes_for_tier`).

```
fn _crc32_update_byte(crc: u32, byte: u8) -> u32:
    var next = crc ^ byte.to_u32()
    var bit = 0
    while bit < 8:
        if (next & 1u32) == 1u32:
            next = (next >> 1) ^ CRC32_POLY_REV
        else:
            next = next >> 1
        bit = bit + 1
    next
```

Pattern: CRC32 computed bit-by-bit per byte (no table). The `crc32_bytes_for_tier` outer loop (`utilities.spl:197`) processes `chunk_width` bytes per iteration but calls `_crc32_update_byte` serially per lane — effectively still byte-at-a-time.

**SIMD opportunity (two levels):**
1. **Table-based CRC32 (TRIVIAL):** Replace bit-loop with a 256-entry lookup table (`crc ^ table[(crc ^ byte) & 0xFF] >> 8`). Yields ~8× over bit-loop independently of SIMD. This is pure algorithmic, no intrinsic needed.
2. **Slice-by-8 / pclmulqdq (MEDIUM):** Use `_mm_clmulepi64_si128` (x86) or `vmull_p64` (ARM) for carryless multiplication. This is the approach used by zlib-ng and achieves 10+ GB/s vs. ~300 MB/s for bit-loop.

**Existing language:** Pure Simple (bit-loop, no lookup table).
**Expected speedup:** 8× (table), 30× (pclmulqdq). Reference: Intel Application Note 323405 "Fast CRC Computation Using PCLMULQDQ."
**Difficulty:** TRIVIAL (table) / MEDIUM (pclmulqdq).

---

## §4 LZ4

### 4.1 Location

Two implementations:
- `src/lib/common/compress/lz4.spl` — primary, typed `[u8]` arrays, SIMD-tier aware via `utilities.spl`.
- `src/lib/nogc_sync_mut/compression/lz4.spl` — secondary wrapper.

### 4.2 Hot-loop pattern H — match-length extension scan [COMPRESS]

**File:line:** `src/lib/common/compress/lz4.spl:34` (`_lz4_match_length`).

```
fn _lz4_match_length(input: [u8], left: i64, right: i64) -> i64:
    var length = 0
    while right + length < input.len() and input[left + length] == input[right + length]:
        length = length + 1
    length
```

Pattern: byte-by-byte comparison until mismatch. Called from `_lz4_compress_block_greedy` (`lz4.spl:75-135`) for every candidate match.

**SIMD opportunity:** Load 16 bytes at `left+length` and `right+length` simultaneously with `_mm_loadu_si128`, XOR, and use `_mm_cmpeq_epi8` + `_mm_movemask_epi8` + `tzcnt` to find the first mismatch byte in one instruction group. This is exactly the "vpcmpeqb + movemask + tzcnt" idiom used by LZ4 C reference implementation. Extends 16 bytes per iteration rather than 1.

**Existing language:** Pure Simple.
**Expected speedup:** ~16× per match extension (up to 16 bytes per SIMD iteration). Net compress throughput impact: 2–5× depending on match density.
**Difficulty:** MEDIUM.

### 4.3 Hot-loop pattern I — 4-byte hash sequence [COMPRESS]

**File:line:** `src/lib/common/compress/lz4.spl:27` (`_lz4_hash_sequence`).

```
fn _lz4_hash_sequence(input: [u8], pos: i64) -> i64:
    val b0 = input[pos].to_i64()
    val b1 = input[pos + 1].to_i64()
    val b2 = input[pos + 2].to_i64()
    val b3 = input[pos + 3].to_i64()
    ((b0 * 251) + (b1 * 509) + (b2 * 1021) + (b3 * 2039)) % LZ4_HASH_SIZE
```

Pattern: 4-byte scalar multiply-sum hash. Called once per input position in the greedy compress loop (`lz4.spl:88`).

**SIMD opportunity:** Use `_mm_set_epi32` + multiply-and-add with a constant coefficient vector to process 4 bytes per single SIMD multiply. In a batch context (multiple positions), SIMD gathers can hash 4 positions simultaneously.

**Existing language:** Pure Simple.
**Expected speedup:** 2–4× in hash throughput (4 hashes in parallel via SIMD multiply).
**Difficulty:** MEDIUM (batch gather complicates the hash-table update order).

### 4.4 Hot-loop pattern J — LZ4 block decompress: literal copy + match copy [DECOMPRESS]

**File:line:** `src/lib/common/compress/lz4.spl:147` (`lz4_decompress_block`).

The block decode loop:
```
while pos < input.len():
    # literal copy
    out = append_bytes(out, input.slice(pos, pos + literal_len))
    # match copy
    val copy_res = append_self_overlap_copy(out, offset, match_len)
```

Both `append_bytes` (`utilities.spl:143`) and `append_self_overlap_copy` (`utilities.spl:160`) are byte-by-byte push loops.

**SIMD opportunity:** Same as §2.4 — `append_self_overlap_copy` can be 16/32-byte SIMD for `offset >= 16`. Additionally, `append_bytes` for the literal copy path is a straightforward `memcpy` — 16–32 bytes per SIMD instruction rather than 1.

**Existing language:** Pure Simple.
**Expected speedup:** 4–8× for long literals and long matches (same analysis as §2.4).
**Difficulty:** MEDIUM.

---

## §5 LZMA2 / XZ

### 5.1 Location

`src/lib/common/compress/lzma2.spl` — 1,100+ lines, pure Simple. Covers both LZMA stream decode and XZ container framing.

### 5.2 Hot-loop pattern K — range coder decode bit [DECOMPRESS]

**File:line:** `src/lib/common/compress/lzma2.spl:165` (`_lzma_decode_bit`), called inside:
- `_lzma_decode_bittree` at `lzma2.spl:199` (8-bit tree, 8 iterations)
- `_lzma_decode_bittree_reverse` at `lzma2.spl:215` (4-bit reverse tree)
- `_lzma_decode_literal` at `lzma2.spl:427` (8-bit adaptive literal decode, two nested `while symbol < 0x100` loops)
- Main decode loop at `lzma2.spl:523` (`while produced < uncompressed_size`)

Pattern: per-bit probabilistic decode using `bound = (range >> 11) * prob`. `prob` is an adaptive probability stored in `pp[idx]` and updated per bit decoded. Each call to `_lzma_decode_bit` reads and writes a single probability entry.

**SIMD opportunity:** **Not applicable.** LZMA's range coder is inherently sequential: each `_lzma_decode_bit` result determines the next `idx` into the probability table (state machine transition). Batching multiple bits is only possible with speculative execution, which LZMA implementations (lzma-sdk, xz-utils) universally avoid in favour of scalar decode. Do **not** attempt to vectorise this path.

**Existing language:** Pure Simple.
**Expected speedup:** N/A (sequential data dependency chain).
**Difficulty:** N/A — do not vectorise.

### 5.3 Hot-loop pattern L — LZMA match copy [DECOMPRESS]

**File:line:** `src/lib/common/compress/lzma2.spl:643`

```
while copied < length:
    val b = dict[dict.len() - st.rep0 - 1]
    dict.push(b)
    produced = produced + 1
    copied = copied + 1
```

Pattern: back-reference copy from dictionary. Same structure as `append_self_overlap_copy`. `rep0` is 0-indexed distance.

**SIMD opportunity:** Same as §2.4 / §4.4: when `st.rep0 >= 16`, copy 16/32 bytes per SIMD iteration instead of 1. When `st.rep0 < length` (RLE expansion), broadcast first `rep0` bytes as a tile.

**Existing language:** Pure Simple.
**Expected speedup:** 4–8× for long non-overlapping matches.
**Difficulty:** MEDIUM.

---

## §6 Brotli

### 6.1 Location

`src/lib/nogc_sync_mut/compression/brotli/` — 4 files (decoder.spl, encoder.spl, bit_reader.spl, bit_writer.spl), all pure Simple.

Note: The decoder at `src/lib/nogc_sync_mut/compression/brotli/decoder.spl:704` and several `_decode_compressed_block` checks use `UnsupportedFeature` returns for multi-block-type inputs (NBLTYPESL/I/D > 1). The decoder is currently limited to single-literal-block-type streams.

### 6.2 Hot-loop pattern M — brotli bit reader refill [DECOMPRESS]

**File:line:** `src/lib/nogc_sync_mut/compression/brotli/bit_reader.spl:35` (`brotli_bits_peek`) and `bit_reader.spl:52` (`brotli_bits_read`).

```
while cur_bits < n:
    cur_buf = cur_buf | (r.data[cur_pos].to_i64() << cur_bits)
    cur_bits = cur_bits + 8
    cur_pos = cur_pos + 1
```

Pattern: LSB-first bit-buffer refill. Appends bytes to a software bit register until `n` bits are available.

**SIMD opportunity:** Prefetch the next 8 bytes into a 64-bit word (`_mm_loadl_epi64`) and use a single shift-and-mask for any `n <= 64` without iteration. This eliminates the `while cur_bits < n` loop entirely and replaces it with a single load + shift, unconditionally. Standard Huffman decode fast-path idiom (zstd bit reader uses this approach: `zstd_bits.spl` already reads 8 bytes at once).

**Existing language:** Pure Simple.
**Expected speedup:** ~2× in bit-read throughput (eliminate refill loop iteration).
**Difficulty:** TRIVIAL (single 8-byte preload).

### 6.3 Hot-loop pattern N — brotli output copy [DECOMPRESS]

**File:line:** `src/lib/nogc_sync_mut/compression/brotli/decoder.spl:704` (`while out.len() < target`) and `decoder.spl:741` (`while k < insert_length`).

Pattern: output copy for insert+copy commands (literal byte insert and back-reference copy). Same byte-push structure as LZ4/zstd match copy.

**SIMD opportunity:** Same as §2.4 — SIMD bulk copy when `distance >= 16`.

**Existing language:** Pure Simple.
**Expected speedup:** 4–8× for large copies.
**Difficulty:** MEDIUM.

---

## §7 General Huffman / FSE Primitives

### 7.1 Location

`src/lib/common/huffman/` — 6 files (tree.spl, codes.spl, decode.spl, encode.spl, types.spl, utilities.spl). Used by standalone Huffman codec, not directly by zstd or gzip (those have their own Huffman implementations).

**File:line (decode):** `src/lib/common/huffman/decode.spl:1`
**File:line (encode):** `src/lib/common/huffman/encode.spl:1`
**File:line (tree):** `src/lib/common/huffman/tree.spl:1`

### 7.2 Hot-loop pattern O — Huffman tree construction (min-heap sort) [COMPRESS]

**File:line:** `src/lib/nogc_sync_mut/compression/gzip/huffman.spl:98` (`huffman_build_tree`) and the node-frequency comparison calls inside the priority queue. Also `huffman_freq_table` inner scan at `huffman.spl:47`.

The gzip `huffman_freq_table` uses a nested loop: for each new token, it scans the existing frequency list to find if the symbol exists. This is O(n·m) with dynamic list append.

**SIMD opportunity:** Same as §3.2 — convert to fixed-size array histogram, then vectorise with SIMD.

**Existing language:** Pure Simple (dynamic list).
**Expected speedup:** 3–5×.
**Difficulty:** MEDIUM.

### 7.3 HPACK Huffman (HTTP/2)

**File:line:** `src/lib/common/hpack/huffman_h2.spl:1`

This implements the fixed static Huffman code for HTTP/2 HPACK headers (RFC 7541 Appendix B). Symbols are 5–30 bits wide, variable-length. The decode inner loop walks a pre-built canonical tree or lookup table.

**SIMD opportunity:** Same category as §2.2 (table-lookup decode). For typical HTTP/2 headers, strings are short; SIMD benefit is small. Not a priority.

**Existing language:** Pure Simple.
**Expected speedup:** Marginal for typical header sizes (<1 KB).
**Difficulty:** MEDIUM.

---

## §8 Shared LZ77 Match Primitives

### 8.1 Location

`src/lib/common/lz77/` — 5 files. Used by gzip and standalone LZ77 compression tests.

### 8.2 Hot-loop pattern P — compare_bytes / find_longest_match [COMPRESS]

**File:line:** `src/lib/common/lz77/match.spl:43` (`compare_bytes`) and `match.spl:68` (`find_longest_match_simple`).

```
fn compare_bytes(data1: list, pos1: i64, data2: list, pos2: i64, max_len: i64) -> i64:
    while i < max_len:
        val b1 = data1[idx1]
        val b2 = data2[idx2]
        if b1 == b2:
            length = length + 1
        else:
            length   # return early
```

`find_longest_match_simple` calls `compare_bytes` for every window position:
```
while search_pos < window_pos:
    val match_len = compare_bytes(window, search_pos, lookahead, lookahead_pos, max_length)
    ...
    search_pos = search_pos + 1
```

Pattern: O(n·W) where n = input bytes, W = window size (up to 32768). This is the classic hash-chain match search. `find_match_with_hash` at `match.spl:95` improves this to O(n·chain_depth) but still calls scalar `compare_bytes` per candidate.

**SIMD opportunity:** Replace `compare_bytes` with a 16-byte SIMD comparison loop (`vpcmpeqb` + `movemask` + `tzcnt`), same as `_lz4_match_length` in §4.2. This provides ~16× speedup per match extension. Additionally, LZ77 benefits from SIMD match search using SIMD-based string searching (shift-or, bitap) to find candidates before doing the byte comparison.

**Existing language:** Pure Simple.
**Expected speedup:** 4–16× per match comparison.
**Difficulty:** MEDIUM.

---

## §M (§9) Hot-Loop Catalog — Top 10 by Leverage

| # | Loop | File:line | Tag | SIMD Opportunity | Difficulty |
|---|------|-----------|-----|-----------------|------------|
| 1 | `append_self_overlap_copy` match copy | `src/lib/common/compress/utilities.spl:160` | DECOMPRESS | 16/32-byte copy for offset≥16; SIMD broadcast tile for RLE | MEDIUM |
| 2 | `_zstd_decode_huffman_stream` literal loop | `src/lib/common/compress/zstd.spl:884` | DECOMPRESS | 4-way parallel Huffman decode (4 streams already split) | HARD |
| 3 | `_lz4_match_length` byte scan | `src/lib/common/compress/lz4.spl:34` | COMPRESS | vpcmpeqb + movemask + tzcnt (16 bytes/iter) | MEDIUM |
| 4 | `compare_bytes` in LZ77 | `src/lib/common/lz77/match.spl:43` | COMPRESS | vpcmpeqb + movemask + tzcnt (16 bytes/iter) | MEDIUM |
| 5 | `crc32_bytes_for_tier` per-byte CRC | `src/lib/common/compress/utilities.spl:191` | DECOMPRESS+COMPRESS | Table-based (TRIVIAL), then pclmulqdq (MEDIUM) | TRIVIAL/MEDIUM |
| 6 | `lz4_decompress_block` literal+match copy | `src/lib/common/compress/lz4.spl:147` | DECOMPRESS | SIMD bulk append via `append_bytes` + `append_self_overlap_copy` | MEDIUM |
| 7 | `_lzma_decode_literal` bittree loop | `src/lib/common/compress/lzma2.spl:427` | DECOMPRESS | Not vectorisable (adaptive per-bit probability chain) | N/A |
| 8 | LZMA match copy | `src/lib/common/compress/lzma2.spl:643` | DECOMPRESS | SIMD bulk copy for rep0≥16 | MEDIUM |
| 9 | `huffman_freq_table` histogram scan | `src/lib/nogc_sync_mut/compression/gzip/huffman.spl:47` | COMPRESS | Fixed-array histogram (no SIMD needed for 8×), then vectorised | MEDIUM |
| 10 | `_zstd_xxh64_bytes_for_tier` hash loop | `src/lib/common/compress/zstd.spl:1125` | DECOMPRESS | Fix dead NEON branch; use SIMD u64 load | MEDIUM |

---

## §M+1 (§10) Pattern Deduplication

The following patterns recur across multiple algorithms, making them candidates for generic primitives.

### Pattern Alpha — "scan until byte mismatch"

Appears in:
- `_lz4_match_length` (`lz4.spl:34`): `while input[left+n] == input[right+n]`
- `compare_bytes` (`lz77/match.spl:43`): `while b1 == b2`

**Generic primitive:** `fn find_first_mismatch(a: [u8], apos: i64, b: [u8], bpos: i64, max: i64) -> i64`
**SIMD implementation:** Load 16 bytes from each side with `_mm_loadu_si128`, XOR, test for zero with `_mm_cmpeq_epi8` + `_mm_movemask_epi8`, then `tzcnt` to find first mismatch. Returns mismatch offset or `max` if all match.

### Pattern Beta — "back-reference copy (possibly overlapping)"

Appears in:
- `append_self_overlap_copy` (`utilities.spl:160`): used by zstd (`zstd.spl:675`) and LZ4 (`lz4.spl:193`)
- LZMA match copy (`lzma2.spl:643`)
- Brotli output copy (`brotli/decoder.spl:741`)

**Generic primitive:** `fn copy_with_offset(out: [u8], offset: i64, count: i64) -> [u8]`
Split into:
- Fast path (`offset >= 32`): SIMD 32-byte copy (`_mm256_loadu_si256` + `_mm256_storeu_si256`)
- Overlap path (`offset < count`): SIMD tile-broadcast for the first `offset` bytes, then bulk copy

### Pattern Gamma — "byte-buffer LSB-first bit refill"

Appears in:
- Brotli bit reader (`bit_reader.spl:35`, `bit_reader.spl:52`)
- zstd backward bit reader (`zstd_bits.spl:1–80`) — already reads 8 bytes at once (more efficient)
- gzip inflate bit reader (similar pattern inferred from `inflate.spl`)

**Generic primitive:** `fn refill64(buf: i64, buf_bits: i64, data: [u8], pos: i64) -> (i64, i64, i64)` — load 8 bytes as u64, shift into buffer, update pos.

Note: zstd's `zstd_bits.spl` backward bit reader is already close to this; brotli's per-byte refill is the outlier.

### Pattern Delta — "byte-frequency histogram"

Appears in:
- `huffman_freq_table` (`huffman.spl:47`): dynamic list O(n·m)
- Any byte-counting loop for entropy estimation

**Generic primitive:** `fn byte_histogram(data: [u8]) -> [i64; 256]` using a fixed 256-entry array. Then vectorise with SIMD: 16-byte loads, scatter-increment using SIMD gather-mask pattern, or interleaved 4-accumulator approach to avoid aliasing.

### Pattern Epsilon — "append_bytes bulk copy"

Appears in:
- `append_bytes` / `append_bytes_range` (`utilities.spl:143`, `utilities.spl:152`)
- Called from zstd sequence execute (`zstd.spl:673`), LZ4 decompress (`lz4.spl:172`), brotli insert

**Generic primitive:** `fn bulk_append(out: [u8], src: [u8], start: i64, end: i64) -> [u8]` with SIMD 16/32-byte copy loop.

---

## §M+2 (§11) Top-3 Recommendations

**Pre-requisite:** Fix open encoder bugs (§1.4) before any encoder-side SIMD work.

### Recommendation 1 — SIMD bulk copy primitive (Pattern Beta + Pattern Epsilon)

**Target:** `append_self_overlap_copy` (`src/lib/common/compress/utilities.spl:160`) and `append_bytes` (`utilities.spl:143`).

**Why first:**
- Touches every decompressed byte for zstd, LZ4, LZMA2, and brotli.
- Non-overlapping case (`offset >= 16`) is a straightforward `memcpy` kernel — lowest implementation risk.
- The tier framework (`CompressionSimdTier`) is already in place and used by the same file.
- A single implementation improvement benefits four algorithms simultaneously.

**Implementation plan:**
1. Add `fast_copy_bytes(src: [u8], src_off: i64, count: i64) -> [u8]` calling a SIMD intrinsic for 16-byte aligned blocks, scalar tail.
2. In `append_self_overlap_copy`: branch on `offset >= 16` → fast path; else scalar.
3. Replace `append_bytes` inner loop with `fast_copy_bytes`.

**Expected speedup:** 4–8× for long matches (>16 bytes), which account for most decompressed volume in typical zstd/LZ4 payloads.
**Difficulty:** MEDIUM.

### Recommendation 2 — CRC32 lookup-table + pclmulqdq (Pattern CRC, §3.4)

**Target:** `_crc32_update_byte` (`src/lib/common/compress/utilities.spl:171`).

**Why second:**
- Current implementation uses a bit-loop (8 iterations per byte) with no lookup table.
- Simply replacing with a 256-entry table (no SIMD at all) gives ~8× improvement — this is TRIVIAL.
- The tier infrastructure at `utilities.spl:182-186` already dispatches on `avx2`/`neon`/`scalar` and the chunk-width loop at `utilities.spl:197` is ready for a SIMD CRC kernel.
- gzip uses this per-file, and zstd's `xxhash32` shares the same file — fixes benefit both.

**Implementation plan:**
1. Add `val CRC32_TABLE: [u32; 256]` computed at module load (or as a static constant).
2. Replace `_crc32_update_byte` bit-loop with a single table lookup.
3. For AVX2 tier: implement slice-by-8 (8 parallel CRC streams combined with XOR).

**Expected speedup:** 8× (table), 30× (pclmulqdq vs. current bit-loop).
**Difficulty:** TRIVIAL (table) / MEDIUM (pclmulqdq).

### Recommendation 3 — Generic byte-mismatch-scan primitive (Pattern Alpha, §4.2 + §8.2)

**Target:** `_lz4_match_length` (`src/lib/common/compress/lz4.spl:34`) and `compare_bytes` (`src/lib/common/lz77/match.spl:43`).

**Why third:**
- LZ4 compress throughput is gated by match extension speed. The C LZ4 reference achieves >1 GB/s largely due to SIMD wild-copy and vectorised comparison.
- Both functions have the identical pattern: scan forward until a byte mismatch, return length. A single SIMD primitive replaces both.
- No data dependencies on external state (unlike FSE/LZMA bit decoders) — genuinely parallelisable.
- Compiler auto-vectorisation hint: the loop body is exactly a SIMD horizontal min search.

**Implementation plan:**
1. Implement `find_first_mismatch(a: [u8], apos: i64, b: [u8], bpos: i64, max: i64) -> i64` using `_mm_loadu_si128` + `_mm_cmpeq_epi8` + `_mm_movemask_epi8` + `tzcnt` for x86-64; `vceqq_u8` + `vminvq_u8` for AArch64 NEON.
2. Replace body of `_lz4_match_length` and `compare_bytes` with calls to this primitive.

**Expected speedup:** 16× per match extension call; net compress throughput 2–5× depending on match density.
**Difficulty:** MEDIUM.

---

## §12 Appendix: xxHash32 Tier Branch Note

`src/lib/common/compress/utilities.spl:247` (`xxhash32_bytes_for_tier`) correctly passes `tier` through but `_xxhash32_process_chunk` (`utilities.spl:230`) always uses `chunk_width = 16` (hard-coded). The outer dispatch at `utilities.spl:256` always passes 16. No AVX2 256-bit path exists yet.

`src/lib/common/compress/zstd.spl:1125` (`_zstd_xxh64_bytes_for_tier`) sets:
```
val chunk_width = if tier == CompressionSimdTier.avx2: 32 else: 32
```
Both branches are 32 — the NEON branch is dead. This is a latent bug; NEON should use 16.

Both require only a one-line fix each; the larger work is adding SIMD load intrinsics.

---

*Document generated 2026-05-02. Scope: J3 / Wave J. All citations are to `src/lib/` only.*
