# Bug: zstd fresh-table literal decoder gap + contradictory fail-closed specs

**Date:** 2026-06-30
**Component:** `src/lib/common/compress/zstd_literals.spl`, `zstd_huf.spl`,
the type-2 (fresh-table compressed) Huffman literal decoder.

## 1. Contradictory specs (UNSATISFIABLE — needs a test-suite decision)

Two specs feed the **byte-identical** 22-byte zstd frame
`28b52ffda00400000055000042800184432010800d00` and demand DIFFERENT errors:

- `zstd_compressed_block_spec.spl:99` ("rejects the host-rejected fresh-table
  single-stream direct-weight candidate") → requires
  `UnsupportedFeature` / "fresh-table compressed literals".
- `zstd_single_sequence_compress_spec.spl:196` ("fails closed on the
  host-rejected direct-weight single-stream candidate") → requires
  `CorruptStream` / "trailing bits".

A deterministic decoder cannot return two different (kind, message) pairs for
identical input. One of these two specs is wrong and must be reconciled by the
spec owner. Current code satisfies compressed_block (kept 14/0) via the
fail-closed literals guard; single_sequence-196 therefore fails.

## 2. Fresh-table literal decoder gap (real decoder work)

The type-2 fresh-table compressed-literals path does not yet decode genuine host
frames (e.g. `zstd -19` output). Empirically, decoding a HOST_VALID type-2
literal section fails in the Huffman-stream / FSE-weight primitives
(`_zstd_decode_huffman_stream`, `_zstd_parse_fse_compressed_weights`, 4-stream
split) before sequences are ever reached. Because of this, the current
`zstd_literals.spl` keeps a blanket fail-closed guard
(`UnsupportedFeature("zstd fresh-table compressed literals are not host-validated")`).

Consequences (left at baseline, NOT the guard's fault):
- `zstd_frame_variants_spec` "decodes a host-generated frame for a mixed payload"
  (1 fail) — needs real type-2 decode.
- `zstd_single_sequence_compress_spec:160` "fails closed on exact host-zstd
  fresh-table … predefined-table sequence" (1 fail) — needs literals to decode
  so the sequence-table gate can fire.

Fix path: make the type-2 fresh-table Huffman literal decoder correctly decode
real host frames AND reject the invalid direct-weight candidate — a
decoder-correctness task, not a guard-ordering one.

## Fixed this session

`zstd_huf_spec` (5/0): validation-order bug in `zstd_huf_weights_to_symbols` —
the "requires at least one weight of 1" check ran before the oversubscription
(power-of-two sum) check, so oversubscribed sets reported the wrong error.
Reordered so oversubscribed/incomplete is detected first.
