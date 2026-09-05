# zstd_fse_compressed_block_deferred_2026-06-15

**Status:** Deferred (not a bug — intentional scope boundary)
**Filed:** 2026-06-15
**Component:** `src/lib/common/compress/typed/zstd_typed.spl`

## What is deferred

Full FSE (Finite State Entropy) compressed-block decode for Zstd frames.
`zstd_decompress` currently returns `ok=false` with message
`"compressed blocks not supported (FSE deferred)"` when it encounters
a Block_Type=2 (Compressed) block.

## What IS implemented (C3 deliverable)

- Zstd frame magic + Frame_Header_Descriptor + FCS encoding/parsing
- Raw blocks (Block_Type=0): encode + decode, split at 128 KB
- RLE blocks (Block_Type=1): decode (expand 1 stored byte × block_size)
- `FseTable.from_normalized_counts`: symbol-spread algorithm per zstd spec §3.1.1
- `FseTable.slots_for_symbol`: verified spread invariant (each symbol gets exactly
  `counts[s]` slots; total == `1<<table_log`)
- `FseTable.decode_symbol_stub`: symbol lookup by state (scaffold only)

## What remains to implement

1. **Reverse-bitstream reader**: zstd reads FSE bitstreams from back to front.
   Needs a `BitReader` variant that starts at the last byte and reads MSB-first
   within bytes, advancing backwards.

2. **FSE decode_symbol**: given current state `s`, read `entries[s].nb_bits` bits
   from the reverse bitstream, compute `next_state = entries[s].baseline + bits`,
   return `entries[s].symbol`. The per-slot `nb_bits` and `baseline` values must
   be computed precisely from the normalized counts (the current scaffold uses an
   approximate `table_log - floor_log2(c)` which is valid for power-of-two counts
   only).

3. **Literals section decode**: Huffman-compressed literals block parsing
   (Literals_Section_Header → Raw/RLE/Huffman/Treeless literals).

4. **Sequences section decode**: decode sequence count + FSE-coded (ll, ml, of)
   tables + sequence execution (LZ77 copy).

5. **Content checksum**: XXH64 over regenerated content (NOT CRC32).
   Current implementation sets Content_Checksum_flag=0 and emits none.

## Why deferred

Full FSE + Huffman + sequences + reverse-bitstream is research-grade work
(~1500 lines of spec-correct Simple). The C3 deliverable is framing +
raw/RLE round-trip + typed FSE scaffold with proved spread invariant,
which is the minimal foundation for codec teams to build on.

## Interop note

Frames produced by `zstd_compress_raw` are valid Zstd frames (raw blocks only)
and can be decompressed by the reference `zstd` CLI:
```
zstd -d < raw_frame.zst
```
Frames with compressed blocks from external tools will be rejected by
`zstd_decompress` until this deferral is resolved.
