# Design: BLAKE3-256, XXH3-128 and hardened gzip (pure Simple)

Plan: `doc/03_plan/lib/crypto/hash_gzip_hardening_2026-10-18.md`.

## BLAKE3 (`src/lib/common/crypto/blake3.spl`)
- One compression function `_b3_compress(cv, block, counter, block_len, flags)`
  on u32 scalar locals; rounds re-bind the 16 message words in place of an
  array permutation.
- A pending compression is an "output node" (8 cv + 16 block words +
  counter/len/flags) so the same value serves as an interior CV or the root.
- Tree: chunks are folded left to right; after chunk `i` the CV stack is
  merged while the chunk count is even (trailing zeros), then the last chunk
  node is folded with the stack right to left. The root node is compressed
  once per 64-byte output block with the block counter (XOF).
- Modes are (key words, flags): hash = (IV, 0); keyed = (key, KEYED_HASH);
  derive = context hashed with DERIVE_KEY_CONTEXT, then used as the key with
  DERIVE_KEY_MATERIAL. Wrong key length fails closed (`[]`).

## XXH3 (`src/lib/common/crypto/xxh3.spl`)
- Scalar port of `xxhash.h`: length-class dispatch (0, 1-3, 4-8, 9-16,
  17-128, 129-240, long), separate 64- and 128-bit mixers.
- Long inputs: 8 u64 accumulators, `stripes_per_block = (secret_len-64)/8`,
  scramble after each block, last stripe at `secret_len - 64 - 7`.
- Seeded long inputs derive a 192-byte custom secret; short inputs mix the
  seed directly. `_mul128` uses 32-bit limbs (no native 128-bit type).
- Result of `xxh3_128` is `[low64, high64]`; `xxh3_128_hex` is canonical
  big-endian (high then low). A secret < 136 bytes fails closed.

## gzip / DEFLATE (`src/lib/nogc_sync_mut/compression/gzip/`)
- `inflate_member(input, start)` = `_inflate_core(member = true)`; gzip members
  must end in a BFINAL block and are decoded back to back (RFC 1952 2.2
  multi-member; output is the concatenation). Raw `inflate` keeps sync-flush leniency for
  RFC 7692 permessage-deflate.
- Huffman validation (RFC 1951 3.2.2/3.2.7): over-subscribed codes always
  rejected; incomplete codes rejected except zlib's single one-bit code for
  lit/len and distance alphabets; HLIT <= 286, HDIST <= 30.
- Back-references are bounds-checked once (`distance <= out.len()`) before
  the copy loop; the loop itself needs no per-byte check.
- Failure is `nil` (facade: `[]`); no partial output is ever returned.
