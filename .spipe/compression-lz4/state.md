# compression-lz4 — state

## Status: CLOSED — 2026-05-20

## Research findings

- `src/lib/common/compress/lz4.spl` already had `lz4_compress_frame` / `lz4_decompress_frame`
  (frame-level API) but was missing the raw block-level API required by the test spec.
- `src/lib/nogc_sync_mut/compression/lz4.spl` is misnamed — it implements RLE, not LZ4.
  Do not rely on it for LZ4 patterns.
- Test spec at `test/unit/lib/common/compress/lz4_spec.spl` imports three symbols via
  `use compress.lz4.{lz4_compress_block, lz4_compress_block_with_level, lz4_decompress_block}`.
- The "repeated data compressed is smaller" test requires actual back-reference encoding
  (store-only path fails the size check for 1000-byte repeated input).
- Plan file: `doc/03_plan/agent_tasks/pure_simple_lz4_zstd_speed_parity.md` Agent A tasks.

## Work done

1. Added to `src/lib/common/compress/lz4.spl`:
   - `lz4_decompress_block(data)` — wraps `_lz4_decode_block(data, 0, data.len())`
   - `lz4_compress_block(data)` — delegates to greedy encoder
   - `lz4_compress_block_with_level(data, level)` — level accepted for API compat, same encoder
   - `_lz4_hash4` — 12-bit Knuth multiplicative hash on 4-byte window
   - `_lz4_match_len` — byte-by-byte match extension
   - `_lz4_emit_sequence` — token + lit-len-ext + literals + LE-offset + match-len-ext
   - `_lz4_emit_last_literals` — terminal literal-only sequence
   - `_lz4_encode_block_compress` — greedy hash-table encoder with 4096-slot table,
     honours LZ4 spec constraints (min match 4, last 5 bytes literal, last match ≥12 from end)
2. Updated `src/lib/common/compress/__init__.spl` to re-export lz4 block and frame symbols.

## Verify

```bash
bin/simple test test/unit/lib/common/compress/lz4_spec.spl --mode=interpreter --clean
```
