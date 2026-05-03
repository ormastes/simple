# Compression Algorithms — Agent Task Plan (2026-05-03)

## Status Summary

| Module | Standard | Status | Tests |
|--------|----------|--------|-------|
| `deflate.spl` | DEFLATE RFC 1951 | Done | 5 pass |
| `gzip.spl` | gzip RFC 1952 | Done | 6 pass |
| `lz4.spl` | LZ4 frame | Done | 5 pass |
| `snappy.spl` | Snappy block | Done | 7 pass |
| `zstd.spl` | Zstd decoder | Done | pass |
| `zstd_huf.spl` | Zstd HUF encoder | Done (W14-A fix) | round-trip pass |
| `zstd_fse.spl` | Zstd FSE encoder | Bug filed | needs fix |
| `lzma2.spl` | LZMA2 range-coded | Done (decoder) | pass |
| Brotli (in zstd area) | Brotli RFC 7932 | Literal+LZ77 done | pass |

## Implemented (8 modules, 12 files)

All compression lives in `src/lib/common/compress/`.

### DEFLATE + gzip (complete)
- `deflate.spl` — RFC 1951 full encoder/decoder (static + dynamic Huffman + stored blocks)
- `gzip.spl` — RFC 1952 wrapper (imports DEFLATE + CRC-32)
- Tests: round-trip, known vectors, CRC check, corruption detection

### LZ4 (complete)
- `lz4.spl` — LZ4 frame format encoder/decoder (370 lines, 22 functions)
- Level 1 = literal-only (search_depth=0); level >= 2 for actual compression
- Fixed `out` → `dest` reserved keyword rename

### Snappy (complete)
- `snappy.spl` — Snappy block compression (294 lines)
- 7 tests including empty, single-byte, repeated pattern, mixed content

### Zstd (decoder complete, encoder partial)
- `zstd.spl` — Full Zstd frame decoder (FSE + Huffman + sequences)
- `zstd_bits.spl` — Backward bit reader with sentinel-bit termination
- `zstd_huf.spl` — Huffman literal encoder (fixed W14-A, round-trip pass)
- `zstd_fse.spl` — FSE encoder (bug at :415, `nb_bits` formula wrong)

### LZMA2 (decoder complete)
- `lzma2.spl` — LZMA2 range-coded decoder

### Brotli (literal + LZ77)
- Literal-only compressed pair (encoder+decoder) done (W9-D)
- LZ77 backreference encoder+decoder done (W14-B)
- Dynamic Huffman NOT done

---

## Remaining Work

### Priority 1 — Fix Zstd FSE Encoder
- **File**: `src/lib/common/compress/zstd_fse.spl:415`
- **Bug**: `nb_bits` formula incorrect for per-symbol encoding
- **Fix**: Restructure to slot-list form, state-walk-driven lookup
- **Agent scope**: 1 agent, ~45-90 min
- **Bug doc**: `doc/08_tracking/bug/zstd_fse_encoder_nb_bits_formula_2026-05-02.md`

### Priority 2 — Brotli Dynamic Huffman
- **Scope**: Extend W14-B's LZ77 encoder with dynamic Huffman code generation
- **Requires**: Context-modeling + prefix code assignment from stream statistics
- **Agent scope**: 1 agent, ~60-90 min

### Priority 3 — Zstd Encoder Levels 4-22
- **Scope**: Full Zstd compression with LDM + dictionary support
- **Requires**: Working FSE encoder (Priority 1)
- **Agent scope**: 2-3 agents, staged

### Priority 4 — LZMA2 Encoder
- **Scope**: LZMA2 range encoder (reverse of existing decoder)
- **Agent scope**: 1 agent, ~60-90 min

---

## Agent Spawn Guide

```
Agent scope: src/lib/common/compress/<module>.spl
Test scope:  test/unit/lib/common/compress/<module>_spec.spl
Verify:      bin/simple test test/unit/lib/common/compress/<spec>.spl
Workaround:  avoid `out`/`val` param names (use `dest`/`input_val`)
```
